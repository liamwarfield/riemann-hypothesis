module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TendstoSmulCocompact
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SigmaContOn

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.ZeroNotMemPreimagePow
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegralNormCvecSq
namespace Formalism.FourierDecayAlt.P.PBK

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace

noncomputable section

section cpic

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def cvec (s : ℕ) (F : ℂ → ℂ → H) (x c : ℂ) : H :=
  (((‖x‖ ^ (s - 1))⁻¹ : ℝ) : ℂ) • F x (c / x ^ (s - 1))

theorem cvec_inner (s : ℕ) (F G : ℂ → ℂ → H) (x x' : ℂ) (hx : x ≠ 0) (hx' : x' ≠ 0) :
    ∫ c, ⟪cvec s F x c, cvec s G x' c⟫_ℂ =
      ∫ D, ⟪F x D, ((‖x ^ (s - 1) / x' ^ (s - 1)‖ : ℝ) : ℂ) • G x' ((x ^ (s - 1) / x' ^ (s - 1)) * D)⟫_ℂ := by
  have ha : x ^ (s - 1) ≠ 0 := pow_ne_zero _ hx
  have hx0 : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hx0' : ‖x'‖ ≠ 0 := norm_ne_zero_iff.mpr hx'
  have hk : ‖x ^ (s - 1)‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr ha)
  have key := integral_comp_mul_C (fun c => ⟪cvec s F x c, cvec s G x' c⟫_ℂ) (x ^ (s - 1)) ha
  have hL : ∫ c, ⟪cvec s F x c, cvec s G x' c⟫_ℂ
      = (‖x ^ (s - 1)‖ ^ 2) • ∫ z, ⟪cvec s F x (x ^ (s - 1) * z), cvec s G x' (x ^ (s - 1) * z)⟫_ℂ := by
    rw [key, smul_smul, mul_inv_cancel₀ hk, one_smul]
  rw [hL, ← integral_smul]
  congr 1
  funext D
  change ‖x ^ (s - 1)‖ ^ 2 • ⟪_, _⟫_ℂ = _
  simp only [cvec]
  rw [mul_div_cancel_left₀ D ha, mul_div_right_comm (x ^ (s - 1)) D (x' ^ (s - 1))]
  have hc : ‖x ^ (s - 1)‖ ^ 2 * (‖x‖ ^ (s - 1))⁻¹ * (‖x'‖ ^ (s - 1))⁻¹
      = ‖x ^ (s - 1) / x' ^ (s - 1)‖ := by
    rw [norm_div, norm_pow, norm_pow]
    field_simp
  rw [inner_smul_left, inner_smul_right, inner_smul_right, Complex.conj_ofReal, Complex.real_smul, ← hc]
  push_cast
  ring

theorem integral_norm_cvec_sq (s : ℕ) (F : ℂ → ℂ → H) (x : ℂ) (hx : x ≠ 0) :
    ∫ c, ‖cvec s F x c‖ ^ 2 = ∫ D, ‖F x D‖ ^ 2 := by
  have ha : (x ^ (s - 1))⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ hx)
  have hr : ‖x‖ ^ (s - 1) ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hx)
  have hce : cvec s F x = fun c => (((‖x‖ ^ (s - 1))⁻¹ : ℝ) : ℂ) • F x ((x ^ (s - 1))⁻¹ * c) := by
    funext c
    simp only [cvec, div_eq_inv_mul]
  rw [hce]
  have h1 : ∀ c, ‖((((‖x‖ ^ (s - 1))⁻¹ : ℝ) : ℂ) • F x ((x ^ (s - 1))⁻¹ * c))‖ ^ 2
      = ((‖x‖ ^ (s - 1)) ^ 2)⁻¹ * ‖F x ((x ^ (s - 1))⁻¹ * c)‖ ^ 2 := by
    intro c
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity), mul_pow, inv_pow]
  simp_rw [h1]
  rw [integral_const_mul, integral_comp_mul_C (fun D => ‖F x D‖ ^ 2) _ ha, smul_eq_mul,
    norm_inv, norm_pow, inv_pow, inv_inv, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero 2 hr), one_mul]

theorem cvec_eq_comp (s : ℕ) (F : ℂ → ℂ → H) (x : ℂ) :
    cvec s F x = fun c => (((‖x‖ ^ (s - 1))⁻¹ : ℝ) : ℂ) • F x ((x ^ (s - 1))⁻¹ * c) := by
  funext c
  simp only [cvec, div_eq_inv_mul]

theorem memLp_cvec (s : ℕ) (F : ℂ → ℂ → H) (x : ℂ) (hx : x ≠ 0) :
    MemLp (F x) 2 volume ↔ MemLp (cvec s F x) 2 volume := by
  have ha : x ^ (s - 1) ≠ 0 := pow_ne_zero _ hx
  have hr : ‖x‖ ^ (s - 1) ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hx)
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [cvec_eq_comp]
    exact (memLp_comp_mul h _ (inv_ne_zero ha)).const_smul _
  · have := (memLp_comp_mul h (x ^ (s - 1)) ha).const_smul ((‖x‖ ^ (s - 1) : ℝ) : ℂ)
    convert this using 1
    congr 1
    funext D
    simp only [cvec, Pi.smul_apply]
    rw [mul_div_cancel_left₀ D ha, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hr, Complex.ofReal_one, one_smul]

theorem cvec_sub (s : ℕ) (F G : ℂ → ℂ → H) (x c : ℂ) :
    cvec s F x c - cvec s G x c = cvec s (fun x D => F x D - G x D) x c := by
  simp only [cvec, smul_sub]

theorem rhoR_pow_eq {s : ℕ} (hs : s ≠ 0) (σ x : ℂ) :
    rhoR s σ x ^ s = x ^ (s - 1) / (x + σ) ^ (s - 1) := by
  unfold rhoR lamR
  rw [Complex.cpow_nat_inv_pow _ hs, div_pow]

theorem norm_rhoR_pow {s : ℕ} (hs : s ≠ 0) (σ x : ℂ) :
    ‖rhoR s σ x‖ ^ s = ‖x ^ (s - 1) / (x + σ) ^ (s - 1)‖ := by
  rw [← norm_pow, rhoR_pow_eq hs]

end cpic

section cpicMain

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem pairD_of_cvec {s : ℕ} (hs : s ≠ 0) (β ε : ℂ) (bt bt' : ℂ → H) (σ x : ℂ) (hx : x ≠ 0) (hxσ : x + σ ≠ 0) :
    ∫ c, ⟪cvec s (fun x D => mainD s β ε bt x D) x c, cvec s (fun x D => mainD s β ε bt' x D) (x + σ) c⟫_ℂ =
      pairD s β ε bt bt' x (x + σ) (rhoR s σ x) := by
  rw [cvec_inner s _ _ x (x + σ) hx hxσ]
  unfold pairD
  rw [rhoR_pow_eq hs, norm_rhoR_pow hs]

end cpicMain

end

end Formalism.FourierDecayAlt.P.PBK
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.AestronglyMeasurableMainD
namespace Formalism.FourierDecayAlt.P.PBK

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace

noncomputable section

open Classical

section abar

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def abar (s : ℕ) (ε : ℂ) (bt : ℂ → H) (D : ℂ) : ℝ := ∑ z ∈ G.rootSet s (ε * D), ‖bt z‖

theorem abar_nonneg (s : ℕ) (ε : ℂ) (bt : ℂ → H) (D : ℂ) : 0 ≤ abar s ε bt D := Finset.sum_nonneg fun _ _ => norm_nonneg _

private lemma norm_psi_lemma (β w : ℂ) : ‖G.psi β w‖ = 1 := by
  simp [G.psi, Complex.norm_exp]

theorem norm_mainD_le (s : ℕ) (β ε : ℂ) (bt : ℂ → H) (x D : ℂ) :
    ‖mainD s β ε bt x D‖ ≤ abar s ε bt D := by
  unfold mainD abar
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun z _ => ?_)
  rw [norm_smul, norm_psi_lemma, one_mul]

theorem mainD_ae_eq {s : ℕ} (hs : s ≠ 0) (β : ℂ) {ε : ℂ} (hε : ε ≠ 0) (bt : ℂ → H) (x : ℂ) :
    mainD s β ε bt x =ᵐ[volume] fun D => ∑ k ∈ Finset.range s,
      G.psi β ((s : ℂ) * NthRootMeasurability.R s k (ε * D) * x) • bt (NthRootMeasurability.R s k (ε * D)) := by
  have h0 : ∀ᵐ D : ℂ ∂volume, D ≠ 0 := by
    rw [ae_iff]; simp
  filter_upwards [h0] with D hD
  unfold mainD
  rw [sum_rootSet_eq_range hs (mul_ne_zero hε hD)]

theorem abar_ae_eq {s : ℕ} (hs : s ≠ 0) {ε : ℂ} (hε : ε ≠ 0) (bt : ℂ → H) :
    abar s ε bt =ᵐ[volume] fun D => ∑ k ∈ Finset.range s, ‖bt (NthRootMeasurability.R s k (ε * D))‖ := by
  have h0 : ∀ᵐ D : ℂ ∂volume, D ≠ 0 := by
    rw [ae_iff]; simp
  filter_upwards [h0] with D hD
  unfold abar
  rw [sum_rootSet_eq_range hs (mul_ne_zero hε hD)]

private lemma measurable_R_lemma (s k : ℕ) : Measurable (NthRootMeasurability.R s k) := by
  unfold NthRootMeasurability.R
  exact measurable_const.mul (measurable_id.pow_const _)

private lemma continuous_psi_lemma_2 (β : ℂ) : Continuous (G.psi β) := by
  unfold G.psi
  fun_prop

theorem aestronglyMeasurable_mainD {s : ℕ} (hs : s ≠ 0) (β : ℂ) {ε : ℂ} (hε : ε ≠ 0) {bt : ℂ → H}
    (hbt : StronglyMeasurable bt) (x : ℂ) : AEStronglyMeasurable (mainD s β ε bt x) volume := by
  refine AEStronglyMeasurable.congr (StronglyMeasurable.aestronglyMeasurable ?_)
    (mainD_ae_eq hs β hε bt x).symm
  have hk : ∀ k ∈ Finset.range s, StronglyMeasurable (fun D : ℂ =>
      G.psi β ((s : ℂ) * NthRootMeasurability.R s k (ε * D) * x) • bt (NthRootMeasurability.R s k (ε * D))) := by
    intro k _
    have hR : Measurable fun D : ℂ => NthRootMeasurability.R s k (ε * D) :=
      (measurable_R_lemma s k).comp (measurable_const.mul measurable_id)
    have hp : Measurable fun D : ℂ => G.psi β ((s : ℂ) * NthRootMeasurability.R s k (ε * D) * x) :=
      (continuous_psi_lemma_2 β).measurable.comp ((measurable_const.mul hR).mul measurable_const)
    exact hp.stronglyMeasurable.smul (hbt.comp_measurable hR)
  have := Finset.stronglyMeasurable_sum (Finset.range s) hk
  convert this using 1 <;> ext D <;> simp

theorem aestronglyMeasurable_abar {s : ℕ} (hs : s ≠ 0) {ε : ℂ} (hε : ε ≠ 0) {bt : ℂ → H}
    (hbt : StronglyMeasurable bt) : AEStronglyMeasurable (abar s ε bt) volume := by
  refine AEStronglyMeasurable.congr (StronglyMeasurable.aestronglyMeasurable ?_)
    (abar_ae_eq hs hε bt).symm
  have hk : ∀ k ∈ Finset.range s, StronglyMeasurable (fun D : ℂ => ‖bt (NthRootMeasurability.R s k (ε * D))‖) := by
    intro k _
    have hR : Measurable fun D : ℂ => NthRootMeasurability.R s k (ε * D) :=
      (measurable_R_lemma s k).comp (measurable_const.mul measurable_id)
    exact (hbt.comp_measurable hR).norm
  have := Finset.stronglyMeasurable_sum (Finset.range s) hk
  convert this using 1 <;> ext D <;> simp

theorem card_rootSet_le (s : ℕ) (a : ℂ) : (G.rootSet s a).card ≤ s := by
  unfold G.rootSet
  exact (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots s a)

theorem jac_norm_bz {s : ℕ} {ε : ℂ} (hε : ‖ε‖ = 1) (bt : ℂ → H) (z : ℂ) :
    ‖ε⁻¹ * ((s : ℂ) * z ^ (s - 1))‖ ^ 2 • ‖bt z‖ ^ 2 = ‖bz s bt z‖ ^ 2 := by
  simp only [bz, norm_smul, norm_mul, norm_inv, hε, inv_one, one_mul, norm_pow,
    Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs, smul_eq_mul, abs_norm]
  rw [abs_of_nonneg (by positivity)]
  ring

theorem memLp_abar {s : ℕ} (hs : s ≠ 0) {ε : ℂ} (hε : ‖ε‖ = 1) {bt : ℂ → H} (hbt : StronglyMeasurable bt)
    (hb : MemLp (bz s bt) 2 volume) :
    MemLp (abar s ε bt) 2 volume ∧ ∫ D, abar s ε bt D ^ 2 ≤ s * ∫ z, ‖bz s bt z‖ ^ 2 := by
  have hε0 : ε ≠ 0 := by rintro rfl; simp at hε
  have hb2 : Integrable (fun z => ‖bz s bt z‖ ^ 2) := (memLp_two_iff_integrable_sq_norm hb.aestronglyMeasurable).1 hb
  have hF : Integrable (fun z => ‖ε⁻¹ * ((s : ℂ) * z ^ (s - 1))‖ ^ 2 • ‖bt z‖ ^ 2) := by
    simp_rw [jac_norm_bz hε bt]; exact hb2
  obtain ⟨hGi, hGeq⟩ := integral_sum_rootSet s hs ε hε0 (fun z => ‖bt z‖ ^ 2) hF
  have hpt : ∀ D, abar s ε bt D ^ 2 ≤ s * ∑ z ∈ G.rootSet s (ε * D), ‖bt z‖ ^ 2 := by
    intro D
    refine (sq_sum_le_card_mul_sum_sq).trans ?_
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast card_rootSet_le s _)
      (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hm := aestronglyMeasurable_abar hs hε0 hbt
  have hsq : Integrable (fun D => abar s ε bt D ^ 2) := by
    refine Integrable.mono' (hGi.const_mul s) (hm.pow 2) (Eventually.of_forall fun D => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hpt D
  refine ⟨(memLp_two_iff_integrable_sq hm).2 hsq, ?_⟩
  calc ∫ D, abar s ε bt D ^ 2 ≤ ∫ D, (s : ℝ) * ∑ z ∈ G.rootSet s (ε * D), ‖bt z‖ ^ 2 :=
        integral_mono hsq (hGi.const_mul s) hpt
    _ = s * ∫ z, ‖bz s bt z‖ ^ 2 := by
        rw [integral_const_mul, hGeq]
        simp_rw [jac_norm_bz hε bt]

theorem memLp_mainD {s : ℕ} (hs : s ≠ 0) (β : ℂ) {ε : ℂ} (hε : ‖ε‖ = 1) {bt : ℂ → H}
    (hbt : StronglyMeasurable bt) (hb : MemLp (bz s bt) 2 volume) (x : ℂ) :
    MemLp (mainD s β ε bt x) 2 volume := by
  have hε0 : ε ≠ 0 := by
    intro h; rw [h, norm_zero] at hε; exact zero_ne_one hε
  refine (memLp_abar hs hε hbt hb).1.of_le (aestronglyMeasurable_mainD hs β hε0 hbt x)
    (ae_of_all _ fun D => ?_)
  rw [Real.norm_of_nonneg (abar_nonneg s ε bt D)]
  exact norm_mainD_le s β ε bt x D

end abar

section moving

theorem dil_dominator {α : Type} {l : Filter α} (ab : ℂ → ℝ) (hab : MemLp ab 2 volume) (lam : α → ℂ)
    (hlam : Tendsto lam l (𝓝 1)) :
    (∀ a D, ‖lam a‖ * ab (lam a * D) ≤ ab D + |‖lam a‖ * ab (lam a * D) - ab D|) ∧
    (∀ᶠ a in l, MemLp (fun D => |‖lam a‖ * ab (lam a * D) - ab D|) 2 volume) ∧
    Tendsto (fun a => ∫ D, |‖lam a‖ * ab (lam a * D) - ab D| ^ 2) l (𝓝 0) := by
  refine ⟨fun a D => by linarith [le_abs_self (‖lam a‖ * ab (lam a * D) - ab D)], ?_, ?_⟩
  · filter_upwards [hlam.eventually_ne one_ne_zero] with a ha
    exact (((memLp_comp_mul hab (lam a) ha).const_mul ‖lam a‖).sub hab).abs
  · have h := (tendsto_dil_real ab hab).comp hlam
    refine h.congr fun a => ?_
    simp only [Function.comp_apply, sq_abs]

end moving

section cut

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem mainD_indicator {s : ℕ} (hs : s ≠ 0) (β : ℂ) {ε : ℂ} (hε : ε ≠ 0) (bt : ℂ → H) (Q : Set ℂ)
    (x D : ℂ) :
    mainD s β ε ({z | ε⁻¹ * z ^ s ∈ Q}.indicator bt) x D = Q.indicator (mainD s β ε bt x) D := by
  have hs0 : 0 < s := Nat.pos_of_ne_zero hs
  have hroot : ∀ z ∈ G.rootSet s (ε * D), ε⁻¹ * z ^ s = D := by
    intro z hz
    have hz' : z ^ s = ε * D := by
      simpa [G.rootSet, Polynomial.mem_nthRoots hs0] using hz
    rw [hz', ← mul_assoc, inv_mul_cancel₀ hε, one_mul]
  unfold mainD
  by_cases hD : D ∈ Q
  · rw [Set.indicator_of_mem hD]
    refine Finset.sum_congr rfl fun z hz => ?_
    rw [Set.indicator_of_mem]
    show ε⁻¹ * z ^ s ∈ Q
    rw [hroot z hz]; exact hD
  · rw [Set.indicator_of_notMem hD]
    refine Finset.sum_eq_zero fun z hz => ?_
    rw [Set.indicator_of_notMem, smul_zero]
    show ε⁻¹ * z ^ s ∉ Q
    rw [hroot z hz]; exact hD

theorem bz_indicator (s : ℕ) (bt : ℂ → H) (Qz : Set ℂ) :
    bz s (Qz.indicator bt) = Qz.indicator (bz s bt) := by
  funext z
  by_cases hz : z ∈ Qz
  · simp [bz, Set.indicator_of_mem hz]
  · simp [bz, Set.indicator_of_notMem hz]

end cut

end

end Formalism.FourierDecayAlt.P.PBK
end

namespace Formalism.FourierDecayAlt.P.PBK

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace

noncomputable section

open Classical

def ann (n : ℕ) : Set ℂ := {D | ((n : ℝ) + 1)⁻¹ ≤ ‖D‖ ∧ ‖D‖ ≤ (n : ℝ) + 1}

theorem isCompact_ann (n : ℕ) : IsCompact (ann n) := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · exact (isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const)
  · exact (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := (n : ℝ) + 1)).subset fun D hD => by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hD.2

theorem zero_notMem_ann (n : ℕ) : (0 : ℂ) ∉ ann n := by
  intro h
  have h1 := h.1
  rw [norm_zero] at h1
  exact absurd h1 (not_le.mpr (by positivity))

theorem ann_mono : Monotone ann := by
  intro m n hmn D hD
  have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
  have h : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by linarith
  exact ⟨le_trans (inv_anti₀ (by positivity) h) hD.1, hD.2.trans h⟩

theorem exists_mem_ann {D : ℂ} (hD : D ≠ 0) : ∃ n, D ∈ ann n := by
  obtain ⟨n, hn⟩ := exists_nat_ge (max ‖D‖ ‖D‖⁻¹)
  have hpos : 0 < ‖D‖ := norm_pos_iff.mpr hD
  refine ⟨n, ?_, ?_⟩
  · have h1 : ‖D‖⁻¹ ≤ (n : ℝ) + 1 :=
      (le_max_right _ _).trans (hn.trans (le_add_of_nonneg_right zero_le_one))
    exact inv_le_of_inv_le₀ hpos h1
  · exact (le_max_left _ _).trans (hn.trans (le_add_of_nonneg_right zero_le_one))

theorem isCompact_preimage_pow {s : ℕ} (hs : s ≠ 0) {ε : ℂ} (hε : ‖ε‖ = 1) {Q : Set ℂ} (hQ : IsCompact Q) :
    IsCompact {z : ℂ | ε⁻¹ * z ^ s ∈ Q} := by
  have hcont : Continuous fun z : ℂ => ε⁻¹ * z ^ s := by fun_prop
  refine Metric.isCompact_of_isClosed_isBounded (hQ.isClosed.preimage hcont) ?_
  obtain ⟨M, hM⟩ := hQ.isBounded.exists_norm_le
  refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := max 1 M)).subset fun z hz => ?_
  have h1 : ‖z‖ ^ s ≤ M := by
    have := hM _ hz
    rwa [norm_mul, norm_inv, hε, inv_one, one_mul, norm_pow] at this
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra hcon
  push_neg at hcon
  have h2 : 1 < ‖z‖ := lt_of_le_of_lt (le_max_left _ _) hcon
  have h3 : ‖z‖ ≤ ‖z‖ ^ s := le_self_pow₀ h2.le hs
  linarith [le_max_right 1 M]

theorem zero_notMem_preimage_pow {s : ℕ} (hs : s ≠ 0) (ε : ℂ) {Q : Set ℂ} (h0 : (0 : ℂ) ∉ Q) :
    (0 : ℂ) ∉ {z : ℂ | ε⁻¹ * z ^ s ∈ Q} := by
  intro h
  apply h0
  simpa [zero_pow hs] using h

section ss

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem norm_sq_le_eta (a u : H) (η : ℝ) (hη : 0 < η) :
    ‖a‖ ^ 2 ≤ (1 + η) * ‖u‖ ^ 2 + (1 + η⁻¹) * ‖u - a‖ ^ 2 := by
  have h1 : ‖a‖ ≤ ‖u‖ + ‖u - a‖ := by
    calc ‖a‖ = ‖u - (u - a)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖u‖ + ‖u - a‖ := norm_sub_le _ _
  have h2 : ‖a‖ ^ 2 ≤ (‖u‖ + ‖u - a‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have e : η * ‖u‖ ^ 2 + η⁻¹ * ‖u - a‖ ^ 2 - 2 * ‖u‖ * ‖u - a‖ = η⁻¹ * (η * ‖u‖ - ‖u - a‖) ^ 2 := by
    field_simp
    ring
  have : 0 ≤ η⁻¹ * (η * ‖u‖ - ‖u - a‖) ^ 2 := by positivity
  nlinarith

theorem stronglyMeasurable_bz (s : ℕ) {bt : ℂ → H} (hbt : StronglyMeasurable bt) :
    StronglyMeasurable (bz s bt) := by
  unfold bz
  have hc : Continuous fun z : ℂ => (((s : ℝ) * ‖z‖ ^ (s - 1) : ℝ) : ℂ) := by fun_prop
  exact hc.stronglyMeasurable.smul hbt

theorem sq_norm_indicator (Qz : Set ℂ) (f : ℂ → H) :
    (fun z => ‖Qz.indicator f z‖ ^ 2) = Qz.indicator (fun z => ‖f z‖ ^ 2) := by
  funext z
  by_cases hz : z ∈ Qz <;> simp [Set.indicator, hz]

theorem memLp_indicator_bz {s : ℕ} {bt : ℂ → H} (hbt : StronglyMeasurable bt) {Qz : Set ℂ}
    (hQz : MeasurableSet Qz) (hloc : IntegrableOn (fun z => ‖bz s bt z‖ ^ 2) Qz) :
    MemLp (Qz.indicator (bz s bt)) 2 volume := by
  have hm : AEStronglyMeasurable (Qz.indicator (bz s bt)) volume :=
    ((stronglyMeasurable_bz s hbt).indicator hQz).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq_norm hm, sq_norm_indicator]
  exact (integrable_indicator_iff hQz).2 hloc

theorem integral_bz_Q_le {s : ℕ} (hs : s ≠ 0) {β : ℂ} (hβ : β ≠ 0) {ε : ℂ} (hε : ‖ε‖ = 1)
    (ut : ℂ → ℂ → H) (bt : ℂ → H) (SS : ℝ) (memU : ∀ x : ℂ, x ≠ 0 → MemLp (ut x) 2 volume)
    (sup : ∀ x : ℂ, x ≠ 0 → ∫ D, ‖ut x D‖ ^ 2 ≤ SS) (hbt : StronglyMeasurable bt) (Q : Set ℂ)
    (hQ : IsCompact Q) (hloc : IntegrableOn (fun z => ‖bz s bt z‖ ^ 2) {z | ε⁻¹ * z ^ s ∈ Q}) (C : ℝ)
    (hC : ∀ x : ℂ, x ≠ 0 → ∀ᵐ D, D ∈ Q → ‖ut x D - mainD s β ε bt x D‖ ≤ C * ‖x‖⁻¹) :
    ∫ z, ‖({z | ε⁻¹ * z ^ s ∈ Q}.indicator (bz s bt)) z‖ ^ 2 ≤ SS := by
  have hε0 : ε ≠ 0 := by rintro rfl; simp at hε
  set Qz : Set ℂ := {z | ε⁻¹ * z ^ s ∈ Q} with hQzdef
  have hQzm : MeasurableSet Qz := (isCompact_preimage_pow hs hε hQ).isClosed.measurableSet
  have hbtQ : StronglyMeasurable (Qz.indicator bt) := hbt.indicator hQzm
  have hbQ : MemLp (bz s (Qz.indicator bt)) 2 volume := by
    rw [bz_indicator]; exact memLp_indicator_bz hbt hQzm hloc
  have hSS0 : 0 ≤ SS := le_trans (integral_nonneg fun _ => sq_nonneg _) (sup 1 one_ne_zero)

  have hsh : Tendsto (fun a : ℂ => (s : ℂ) * ((fun _ : ℂ => (1 : ℂ)) a * id a - id a)) (cocompact ℂ) (𝓝 0) := by
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℂ => (0 : ℂ)) (cocompact ℂ) (𝓝 0))
  have hne : ∀ ζ ∈ G.rootSet s 1, ζ ≠ 1 →
      Tendsto (fun a : ℂ => ζ * (fun _ : ℂ => (1 : ℂ)) a * id a - id a) (cocompact ℂ) (cocompact ℂ) := by
    intro ζ _ h1
    refine (tendsto_smul_cocompact (ζ - 1) (sub_ne_zero.2 h1) id tendsto_id).congr fun a => ?_
    simp only [id]
    ring
  have hT := tendsto_pairD hs hβ hε hbQ hbQ id id (fun _ => (1 : ℂ)) 0
    (Eventually.of_forall fun _ => one_ne_zero) tendsto_const_nhds hsh hne
  set L : ℝ := ∫ z, ‖bz s (Qz.indicator bt) z‖ ^ 2 with hL
  have hinner : ∀ v : H, ⟪v, v⟫_ℂ = ((‖v‖ ^ 2 : ℝ) : ℂ) := fun v => by
    rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
  have hval : ∫ z, G.psi β (0 * z) • ⟪bz s (Qz.indicator bt) z, bz s (Qz.indicator bt) z⟫_ℂ = (L : ℂ) := by
    have hψ0 : ∀ z, G.psi β (0 * z) = 1 := fun z => by simp [G.psi]
    simp_rw [hψ0, one_smul, hinner]
    rw [hL, integral_complex_ofReal]
  rw [hval] at hT

  set f : ℂ → ℝ := fun x => ∫ D, ‖mainD s β ε (Qz.indicator bt) x D‖ ^ 2 with hf
  have hpair : ∀ x, pairD s β ε (Qz.indicator bt) (Qz.indicator bt) x x 1 = (f x : ℂ) := by
    intro x
    simp only [pairD, norm_one, one_pow, Complex.ofReal_one, one_smul, one_mul, hinner, hf]
    rw [integral_complex_ofReal]
  have hfT : Tendsto f (cocompact ℂ) (𝓝 L) := by
    have := (Complex.continuous_re.tendsto _).comp hT
    simpa [Function.comp_def, hpair] using this

  have hbound : ∀ η : ℝ, 0 < η → L ≤ (1 + η) * SS := by
    intro η hη
    obtain ⟨vQ, hvQ⟩ : ∃ v : ℝ, v = (volume Q).toReal := ⟨_, rfl⟩
    have hg : Tendsto (fun x : ℂ => (1 + η) * SS + (1 + η⁻¹) * (C * ‖x‖⁻¹) ^ 2 * vQ) (cocompact ℂ)
        (𝓝 ((1 + η) * SS)) := by
      have h0 : Tendsto (fun x : ℂ => ‖x‖⁻¹) (cocompact ℂ) (𝓝 0) :=
        tendsto_inv_atTop_zero.comp tendsto_norm_cocompact_atTop
      have h1 : Tendsto (fun x : ℂ => (1 + η) * SS + (1 + η⁻¹) * (C * ‖x‖⁻¹) ^ 2 * vQ) (cocompact ℂ)
          (𝓝 ((1 + η) * SS + (1 + η⁻¹) * (C * 0) ^ 2 * vQ)) :=
        tendsto_const_nhds.add ((tendsto_const_nhds.mul ((tendsto_const_nhds.mul h0).pow 2)).mul tendsto_const_nhds)
      simpa using h1
    refine le_of_tendsto_of_tendsto hfT hg ?_
    filter_upwards [eventually_ne_cocompact 0] with x hx
    have hmD : MemLp (mainD s β ε (Qz.indicator bt) x) 2 volume := memLp_mainD hs β hε hbtQ hbQ x
    have i1 : Integrable (fun D => ‖mainD s β ε (Qz.indicator bt) x D‖ ^ 2) :=
      (memLp_two_iff_integrable_sq_norm hmD.aestronglyMeasurable).1 hmD
    have i2 : Integrable (fun D => ‖ut x D‖ ^ 2) := (memLp_two_iff_integrable_sq_norm (memU x hx).aestronglyMeasurable).1 (memU x hx)
    have hQm : MeasurableSet Q := hQ.isClosed.measurableSet
    have i3 : Integrable (Q.indicator fun _ => (1 + η⁻¹) * (C * ‖x‖⁻¹) ^ 2) :=
      (integrableOn_const hQ.measure_lt_top.ne).integrable_indicator hQm
    have hpt : ∀ᵐ D, ‖mainD s β ε (Qz.indicator bt) x D‖ ^ 2 ≤
        (1 + η) * ‖ut x D‖ ^ 2 + Q.indicator (fun _ => (1 + η⁻¹) * (C * ‖x‖⁻¹) ^ 2) D := by
      filter_upwards [hC x hx] with D hD
      rw [mainD_indicator hs β hε0 bt Q x D]
      by_cases hDQ : D ∈ Q
      · rw [Set.indicator_of_mem hDQ, Set.indicator_of_mem hDQ]
        have hr := hD hDQ
        have hr2 : ‖ut x D - mainD s β ε bt x D‖ ^ 2 ≤ (C * ‖x‖⁻¹) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hr 2
        have := norm_sq_le_eta (mainD s β ε bt x D) (ut x D) η hη
        have hc : 0 ≤ 1 + η⁻¹ := by positivity
        nlinarith
      · rw [Set.indicator_of_notMem hDQ, Set.indicator_of_notMem hDQ, norm_zero]
        have : 0 ≤ (1 + η) * ‖ut x D‖ ^ 2 := by positivity
        simpa using this
    calc f x ≤ ∫ D, ((1 + η) * ‖ut x D‖ ^ 2 + Q.indicator (fun _ => (1 + η⁻¹) * (C * ‖x‖⁻¹) ^ 2) D) :=
          integral_mono_ae i1 ((i2.const_mul _).add i3) hpt
      _ = (1 + η) * (∫ D, ‖ut x D‖ ^ 2) + (1 + η⁻¹) * (C * ‖x‖⁻¹) ^ 2 * vQ := by
          have e1 : ∫ D, ((1 + η) * ‖ut x D‖ ^ 2 + Q.indicator (fun _ => (1 + η⁻¹) * (C * ‖x‖⁻¹) ^ 2) D) =
              (1 + η) * (∫ D, ‖ut x D‖ ^ 2) + ∫ D, Q.indicator (fun _ => (1 + η⁻¹) * (C * ‖x‖⁻¹) ^ 2) D := by
            rw [integral_add (i2.const_mul _) i3, integral_const_mul]
          have e2 : ∫ D, Q.indicator (fun _ => (1 + η⁻¹) * (C * ‖x‖⁻¹) ^ 2) D =
              (1 + η⁻¹) * (C * ‖x‖⁻¹) ^ 2 * vQ := by
            rw [integral_indicator hQm, setIntegral_const, smul_eq_mul, hvQ, Measure.real, mul_comm]
          rw [e1, e2]
      _ ≤ (1 + η) * SS + (1 + η⁻¹) * (C * ‖x‖⁻¹) ^ 2 * vQ := by
          have := mul_le_mul_of_nonneg_left (sup x hx) (by positivity : (0 : ℝ) ≤ 1 + η)
          linarith

  rw [← bz_indicator]
  refine le_of_forall_pos_lt_add fun δ hδ => ?_
  have hη : 0 < δ / (SS + 1) := by positivity
  have h1 := hbound _ hη
  have h2 : (1 + δ / (SS + 1)) * SS < SS + δ := by
    have : δ / (SS + 1) * SS < δ := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith
    nlinarith
  linarith

end ss

end

end Formalism.FourierDecayAlt.P.PBK
end

namespace Formalism.FourierDecayAlt.P.PBK

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace ENNReal

noncomputable section

open Classical

section ss2

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem memLp_bz_of_sup {s : ℕ} (hs : s ≠ 0) {β : ℂ} (hβ : β ≠ 0) {ε : ℂ} (hε : ‖ε‖ = 1)
    (ut : ℂ → ℂ → H) (bt : ℂ → H) (SS : ℝ) (memU : ∀ x : ℂ, x ≠ 0 → MemLp (ut x) 2 volume)
    (sup : ∀ x : ℂ, x ≠ 0 → ∫ D, ‖ut x D‖ ^ 2 ≤ SS) (hbt : StronglyMeasurable bt)
    (hloc : ∀ K : Set ℂ, IsCompact K → (0 : ℂ) ∉ K → IntegrableOn (fun z => ‖bz s bt z‖ ^ 2) K)
    (germ : ∀ K : Set ℂ, IsCompact K → (0 : ℂ) ∉ K → ∃ C : ℝ, ∀ x : ℂ, x ≠ 0 →
      ∀ᵐ D, D ∈ K → ‖ut x D - mainD s β ε bt x D‖ ≤ C * ‖x‖⁻¹) :
    MemLp (bz s bt) 2 volume ∧ ∫ z, ‖bz s bt z‖ ^ 2 ≤ SS := by
  have hSS : 0 ≤ SS := (integral_nonneg fun D => sq_nonneg ‖ut 1 D‖).trans (sup 1 one_ne_zero)
  have hε0 : ε ≠ 0 := by
    intro h; rw [h, norm_zero] at hε; exact zero_ne_one hε
  let K : ℕ → Set ℂ := fun n => {z : ℂ | ε⁻¹ * z ^ s ∈ ann n}
  have hKc : ∀ n, IsCompact (K n) := fun n => isCompact_preimage_pow hs hε (isCompact_ann n)
  have hK0 : ∀ n, (0 : ℂ) ∉ K n := fun n => zero_notMem_preimage_pow hs ε (zero_notMem_ann n)
  have hKm : ∀ n, MeasurableSet (K n) := fun n => (hKc n).isClosed.measurableSet
  have hbm : StronglyMeasurable (bz s bt) := stronglyMeasurable_bz s hbt
  have hmem : ∀ n, MemLp ((K n).indicator (bz s bt)) 2 volume := fun n =>
    memLp_indicator_bz hbt (hKm n) (hloc _ (hKc n) (hK0 n))
  have hbound : ∀ n, ∫ z, ‖(K n).indicator (bz s bt) z‖ ^ 2 ≤ SS := fun n => by
    obtain ⟨C, hC⟩ := germ (ann n) (isCompact_ann n) (zero_notMem_ann n)
    exact integral_bz_Q_le hs hβ hε ut bt SS memU sup hbt (ann n) (isCompact_ann n)
      (hloc _ (hKc n) (hK0 n)) C hC
  let g : ℕ → ℂ → ℝ≥0∞ := fun n z => ENNReal.ofReal (‖(K n).indicator (bz s bt) z‖ ^ 2)
  have hgm : ∀ n, Measurable (g n) := fun n =>
    ENNReal.measurable_ofReal.comp (((hbm.indicator (hKm n)).norm.measurable).pow_const 2)
  have hKmono : Monotone K := fun m n hmn z hz => ann_mono hmn hz
  have hgmono : Monotone g := by
    intro m n hmn z
    apply ENNReal.ofReal_le_ofReal
    by_cases hz : z ∈ K m
    · simp only [Set.indicator_of_mem hz, Set.indicator_of_mem (hKmono hmn hz), le_refl]
    · rw [Set.indicator_of_notMem hz, norm_zero, zero_pow two_ne_zero]
      positivity
  have hgn : ∀ n, ∫⁻ z, g n z ≤ ENNReal.ofReal SS := fun n => by
    have hi : Integrable (fun z => ‖(K n).indicator (bz s bt) z‖ ^ 2) :=
      (memLp_two_iff_integrable_sq_norm (hmem n).aestronglyMeasurable).1 (hmem n)
    show ∫⁻ z, ENNReal.ofReal (‖(K n).indicator (bz s bt) z‖ ^ 2) ≤ _
    rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun z => sq_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (hbound n)
  have hsup : (fun z => ENNReal.ofReal (‖bz s bt z‖ ^ 2)) =ᵐ[volume] fun z => ⨆ n, g n z := by
    have h0 : ∀ᵐ z : ℂ ∂volume, z ≠ 0 := by
      rw [ae_iff]; simp
    filter_upwards [h0] with z hz
    have hw : ε⁻¹ * z ^ s ≠ 0 := mul_ne_zero (inv_ne_zero hε0) (pow_ne_zero _ hz)
    obtain ⟨n, hn⟩ := exists_mem_ann hw
    apply le_antisymm
    · refine le_iSup_of_le n (le_of_eq ?_)
      show ENNReal.ofReal (‖bz s bt z‖ ^ 2) = ENNReal.ofReal (‖(K n).indicator (bz s bt) z‖ ^ 2)
      rw [Set.indicator_of_mem (show z ∈ K n from hn)]
    · refine iSup_le fun m => ENNReal.ofReal_le_ofReal ?_
      by_cases hzm : z ∈ K m
      · simp only [Set.indicator_of_mem hzm, le_refl]
      · rw [Set.indicator_of_notMem hzm, norm_zero, zero_pow two_ne_zero]
        positivity
  have hlin : ∫⁻ z, ENNReal.ofReal (‖bz s bt z‖ ^ 2) ≤ ENNReal.ofReal SS := by
    rw [lintegral_congr_ae hsup, lintegral_iSup hgm hgmono]
    exact iSup_le hgn
  have hint : Integrable (fun z => ‖bz s bt z‖ ^ 2) := by
    refine ⟨(hbm.norm.measurable.pow_const 2).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun z => sq_nonneg _)]
    exact lt_of_le_of_lt hlin ENNReal.ofReal_lt_top
  refine ⟨(memLp_two_iff_integrable_sq_norm hbm.aestronglyMeasurable).2 hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun z => sq_nonneg _)
    (hbm.norm.measurable.pow_const 2).aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal hSS hlin

end ss2

end

end Formalism.FourierDecayAlt.P.PBK
