module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLimENF

@[expose] public section

section -- merged from CompanionTheory.AutomorphicTheory.DiscreteGroupWaves.NFTopCpt
section -- merged from CompanionTheory.AutomorphicTheory.DiscreteGroupWaves.NFTopSq
section -- merged from CompanionTheory.AutomorphicTheory.DiscreteGroupWaves.IntegralEqOfSqrtCauchy
namespace CompanionTheory.NFCpt

open MeasureTheory Filter Topology

theorem ae_coords_ne_zero (n : ℕ) : ∀ᵐ c : Fin n → ℂ, ∀ a, c a ≠ 0 := by
  rw [ae_all_iff]
  intro a
  have h : (volume : Measure (Fin n → ℂ)) {c | c a = 0} = 0 := Measure.pi_hyperplane _ a 0
  rw [ae_iff]
  simpa using h

theorem ae_ne_zero_c : ∀ᵐ t : ℂ, t ≠ 0 := by
  rw [ae_iff]
  simp

theorem tower_integral : ∀ (n : ℕ) (E : (j : ℕ) → (Fin j → ℂ) → ℝ),
    AEStronglyMeasurable (E n) volume → (∀ c, (∀ a, c a ≠ 0) → 0 ≤ E n c) →
    (∀ j, j < n → ∀ c : Fin j → ℂ, (∀ a, c a ≠ 0) →
      Integrable (fun t : ℂ => E (j + 1) (Fin.snoc c t)) ∧ ∫ t : ℂ, E (j + 1) (Fin.snoc c t) = E j c) →
    Integrable (E n) ∧ ∫ c, E n c = E 0 (fun a => a.elim0)
  | 0, E, _, _, _ => by
    have e : E 0 = fun _ => E 0 (fun a => a.elim0) := funext fun c => congrArg _ (Subsingleton.elim _ _)
    refine ⟨by rw [e]; exact integrable_const _, ?_⟩
    rw [e, integral_const]
    simp [Measure.real, volume_pi]
  | n + 1, E, hm, h0, hs => by
    let e : (Fin (n + 1) → ℂ) ≃ᵐ (Fin n → ℂ) × ℂ :=
      (MeasurableEquiv.piFinSuccAbove (fun _ => ℂ) (Fin.last n)).trans MeasurableEquiv.prodComm
    have hmp : MeasurePreserving e volume volume :=
      (Measure.measurePreserving_swap).comp (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℂ) (Fin.last n))
    have he : ∀ q : (Fin n → ℂ) × ℂ, e.symm q = Fin.snoc q.1 q.2 := by
      intro q
      apply e.injective
      rw [e.apply_symm_apply]
      simp [e, MeasurableEquiv.piFinSuccAbove]
      ext <;> rfl
    set G : (Fin n → ℂ) × ℂ → ℝ := fun q => E (n + 1) (Fin.snoc q.1 q.2) with hG
    have hGe : G = E (n + 1) ∘ e.symm := funext fun q => by simp [hG, he]
    have hGm : AEStronglyMeasurable G ((volume : Measure (Fin n → ℂ)).prod (volume : Measure ℂ)) := by
      rw [hGe]
      exact hm.comp_measurePreserving (hmp.symm e)
    have hGpos : ∀ c : Fin n → ℂ, (∀ a, c a ≠ 0) → ∀ᵐ t : ℂ, 0 ≤ G (c, t) := by
      intro c hc
      filter_upwards [ae_ne_zero_c] with t ht
      refine h0 _ fun a => ?_
      induction a using Fin.lastCases with
      | last => simpa using ht
      | cast i => simpa using hc i
    have hae : (fun c : Fin n → ℂ => ∫ t, G (c, t)) =ᵐ[volume] E n := by
      filter_upwards [ae_coords_ne_zero n] with c hc
      exact (hs n (Nat.lt_succ_self n) c hc).2
    have hmn : AEStronglyMeasurable (E n) volume := hGm.integral_prod_right'.congr hae
    have h0n : ∀ c, (∀ a, c a ≠ 0) → 0 ≤ E n c := by
      intro c hc
      rw [← (hs n (Nat.lt_succ_self n) c hc).2]
      exact integral_nonneg_of_ae (hGpos c hc)
    have ih : Integrable (E n) ∧ ∫ c, E n c = E 0 (fun a => a.elim0) :=
      tower_integral n E hmn h0n fun j hj => hs j (Nat.lt_succ_of_lt hj)
    have hGI : Integrable G ((volume : Measure (Fin n → ℂ)).prod (volume : Measure ℂ)) := by
      rw [integrable_prod_iff hGm]
      refine ⟨?_, ?_⟩
      · filter_upwards [ae_coords_ne_zero n] with c hc
        exact (hs n (Nat.lt_succ_self n) c hc).1
      · refine (And.left ih).congr ?_
        filter_upwards [ae_coords_ne_zero n] with c hc
        rw [← (hs n (Nat.lt_succ_self n) c hc).2]
        refine integral_congr_ae ?_
        filter_upwards [hGpos c hc] with t ht
        exact (Real.norm_of_nonneg ht).symm
    refine ⟨?_, ?_⟩
    · have : E (n + 1) = G ∘ e := funext fun c => by simp [hGe]
      rw [this]
      exact (hmp.integrable_comp_emb e.measurableEmbedding).2 hGI
    · have h1 : ∫ c, E (n + 1) c = ∫ q, G q ∂((volume : Measure (Fin n → ℂ)).prod (volume : Measure ℂ)) := by
        have := hmp.integral_comp' G
        rw [← show ∫ q, G q = ∫ q, G q ∂((volume : Measure (Fin n → ℂ)).prod (volume : Measure ℂ)) from rfl, ← this]
        refine integral_congr_ae (Eventually.of_forall fun c => ?_)
        simp [hGe]
      rw [h1, integral_prod G hGI, integral_congr_ae hae, And.right ih]

theorem abs_sub_le_of_sqrt {a b d δ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 ≤ d) (hδ : 0 < δ)
    (h : |Real.sqrt a - Real.sqrt b| ≤ Real.sqrt d) : |a - b| ≤ d / δ + δ * (a + b) := by
  set x := Real.sqrt a
  set y := Real.sqrt b
  set z := Real.sqrt d
  have hx : a = x ^ 2 := (Real.sq_sqrt ha).symm
  have hy : b = y ^ 2 := (Real.sq_sqrt hb).symm
  have hz : d = z ^ 2 := (Real.sq_sqrt hd).symm
  have hx0 : 0 ≤ x := Real.sqrt_nonneg _
  have hy0 : 0 ≤ y := Real.sqrt_nonneg _
  have hz0 : 0 ≤ z := Real.sqrt_nonneg _
  have e : |a - b| = |x - y| * (x + y) := by
    rw [hx, hy, show x ^ 2 - y ^ 2 = (x - y) * (x + y) by ring, abs_mul, abs_of_nonneg (add_nonneg hx0 hy0)]
  rw [e, hx, hy, hz]
  have h1 : |x - y| * (x + y) ≤ z * (x + y) := mul_le_mul_of_nonneg_right h (add_nonneg hx0 hy0)
  refine h1.trans ?_
  rw [div_add' _ _ _ hδ.ne', le_div_iff₀ hδ]
  nlinarith [sq_nonneg (z - δ * x), sq_nonneg (z - δ * y), sq_nonneg (δ * x), sq_nonneg (δ * y), sq_nonneg z]

theorem integral_eq_of_sqrt_cauchy {α : Type*} [MeasurableSpace α] {μ : Measure α} {q : ℕ → α → ℝ} {v : α → ℝ}
    {d : ℕ → ℕ → α → ℝ} {a : ℝ} (hq : ∀ n, Integrable (q n) μ) (hq0 : ∀ n x, 0 ≤ q n x)
    (hd : ∀ n m, Integrable (d n m) μ) (hd0 : ∀ n m x, 0 ≤ d n m x)
    (htri : ∀ n m x, |Real.sqrt (q n x) - Real.sqrt (q m x)| ≤ Real.sqrt (d n m x))
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => q n x) atTop (𝓝 (v x)))
    (ha : Tendsto (fun n => ∫ x, q n x ∂μ) atTop (𝓝 a))
    (hC : ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ n m, N ≤ n → N ≤ m → ∫ x, d n m x ∂μ ≤ η) :
    Integrable v μ ∧ ∫ x, v x ∂μ = a := by
  have hv : AEStronglyMeasurable v μ := aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hq n).1) hlim
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ n, ∫ x, q n x ∂μ ≤ B := by
    obtain ⟨B, hB⟩ := ha.bddAbove_range
    exact ⟨B, fun n => hB ⟨n, rfl⟩⟩
  have hB0 : 0 ≤ B := (integral_nonneg (hq0 0)).trans (hB 0)
  have key : ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ n, N ≤ n → ∫⁻ x, ‖q n x - v x‖ₑ ∂μ ≤ ENNReal.ofReal η := by
    intro η hη
    set δ : ℝ := η / (4 * (B + 1)) with hδdef
    have hδ : 0 < δ := by positivity
    obtain ⟨N, hN⟩ := hC (δ * (η / 2)) (by positivity)
    refine ⟨N, fun n hn => ?_⟩
    have hnm : ∀ m, N ≤ m → ∫⁻ x, ‖q n x - q m x‖ₑ ∂μ ≤ ENNReal.ofReal η := by
      intro m hm
      have hI : Integrable (fun x => d n m x / δ + δ * (q n x + q m x)) μ :=
        ((hd n m).div_const δ).add (((hq n).add (hq m)).const_mul δ)
      have h1 : ∫⁻ x, ‖q n x - q m x‖ₑ ∂μ ≤ ∫⁻ x, ENNReal.ofReal (d n m x / δ + δ * (q n x + q m x)) ∂μ := by
        refine lintegral_mono fun x => ?_
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (abs_sub_le_of_sqrt (hq0 n x) (hq0 m x) (hd0 n m x) hδ (htri n m x))
      refine h1.trans ?_
      rw [← ofReal_integral_eq_lintegral_ofReal hI (Eventually.of_forall fun x => by
        have := hd0 n m x; have := hq0 n x; have := hq0 m x; positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have hI2 : Integrable (fun x => δ * (q n x + q m x)) μ := ((hq n).add (hq m)).const_mul δ
      rw [integral_add ((hd n m).div_const δ) hI2, integral_div, integral_const_mul, integral_add (hq n) (hq m)]
      have h2 : (∫ x, d n m x ∂μ) / δ ≤ η / 2 := by
        rw [div_le_iff₀ hδ]; linarith [hN n m hn hm]
      have h3 : δ * (∫ x, q n x ∂μ + ∫ x, q m x ∂μ) ≤ δ * (2 * (B + 1)) :=
        mul_le_mul_of_nonneg_left (by linarith [hB n, hB m]) hδ.le
      have h4 : δ * (2 * (B + 1)) = η / 2 := by rw [hδdef]; field_simp; ring
      linarith
    have hae : ∀ᵐ x ∂μ, ‖q n x - v x‖ₑ = liminf (fun m => ‖q n x - q m x‖ₑ) atTop := by
      filter_upwards [hlim] with x hx
      exact ((continuous_enorm.tendsto _).comp (tendsto_const_nhds.sub hx)).liminf_eq.symm
    rw [lintegral_congr_ae hae]
    refine (lintegral_liminf_le' fun m => ((hq n).1.sub (hq m).1).enorm).trans ?_
    calc liminf (fun m => ∫⁻ x, ‖q n x - q m x‖ₑ ∂μ) atTop
        ≤ liminf (fun _ : ℕ => ENNReal.ofReal η) atTop :=
          liminf_le_liminf (eventually_atTop.2 ⟨N, hnm⟩)
      _ = ENNReal.ofReal η := liminf_const _
  have hvi : Integrable v μ := by
    obtain ⟨N, hN⟩ := key 1 one_pos
    have hd₁ : Integrable (fun x => q N x - v x) μ :=
      ⟨(hq N).1.sub hv, (hN N le_rfl).trans_lt ENNReal.ofReal_lt_top⟩
    exact ((hq N).sub hd₁).congr (ae_of_all _ fun x => by simp)
  refine ⟨hvi, tendsto_nhds_unique ?_ ha⟩
  rw [Metric.tendsto_atTop]
  intro η hη
  obtain ⟨N, hN⟩ := key (η / 2) (by linarith)
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_eq_norm, ← integral_sub (hq n) hvi]
  have h1 := (enorm_integral_le_lintegral_enorm (fun x => q n x - v x)).trans (hN n hn)
  rw [← ofReal_norm, ENNReal.ofReal_le_ofReal_iff (by linarith)] at h1
  linarith

end CompanionTheory.NFCpt
end

namespace CompanionTheory.NFCpt

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP Filter Topology MeasureTheory

noncomputable section

open Classical

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

abbrev SqIx (P : M.Par) (w : List C.Letter) : Type := Option (Wd.Ix (Fin w.length) × M.Ty P)

def sqW (p : KB.Pl P Wp Wq) (w : List C.Letter) (γ : C.LPt) : SqIx P w → ℝ
  | none => if w = [] then Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) γ) else 0
  | some q => if w = [] then 0 else
      Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) γ) * Top.dH P p.l0 (TBB.TTp p) w γ q.1 q.2

def sqX (p : KB.Pl P Wp Wq) (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (γ : C.LPt) :
    SqIx P w → (Wq →L[ℂ] Wp)
  | none => p.V H γ
  | some q => (p.TP.E q.2).comp (p.V (p.Θ.Θ w q.1 H) γ)

theorem hsInner_self_re (A : Wq →L[ℂ] Wp) : (B.hsInner A A).re = ‖B.hsVec A‖ ^ 2 := by
  unfold B.hsInner
  rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (B.hsVec A)]
  norm_cast

theorem V_of_not (p : KB.Pl P Wp Wq) (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) {γ : C.LPt}
    (hγ : ¬ D.IsLocPt γ (P.r + 1)) : p.V H γ = 0 := by
  unfold KB.Pl.V D.vecV
  rw [dite_eq_right fun h => hγ h.1]

theorem ew_top_eq (p : KB.Pl P Wp Wq) (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (γ : C.LPt) :
    TBB.Ew p (fun _ => 1) H (P.r + 1) w γ = ∑ i : SqIx P w, sqW p w γ i ^ 2 * ‖B.hsVec (sqX p H w γ i)‖ ^ 2 := by
  have hn : TBB.normC (fun _ => (1 : ℝ)) w = 1 := by simp [TBB.normC]
  unfold TBB.Ew TBB.NP
  rw [Complex.re_ofReal_mul, hn, div_one, Fintype.sum_option]
  by_cases hγ : D.IsLocPt γ (P.r + 1)
  · unfold KB.Pl.RR D.RRplace
    rw [dite_eq_left ⟨hγ, hγ⟩, dite_eq_right (by omega), if_pos rfl]
    by_cases hw : w = []
    · rw [if_pos hw, hsInner_self_re]
      simp only [sqW, sqX, if_pos hw, KB.Pl.V]
      simp [sq]
    · rw [if_neg hw]
      unfold Top.topOf
      simp only [sqW, sqX, if_neg hw, KB.Pl.V, Complex.re_sum, Complex.re_ofReal_mul, hsInner_self_re,
        Fintype.sum_prod_type, Finset.mul_sum, TBB.TTp]
      rw [show (0 : ℝ) ^ 2 * ‖B.hsVec (D.vecV p.T.base p.ν' p.m₀ H γ)‖ ^ 2 = 0 by simp, zero_add]
      refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun ρ _ => ?_
      ring
  · have h0 : p.RR H (P.r + 1) w γ γ = 0 := by
      unfold KB.Pl.RR D.RRplace
      rw [dite_eq_right fun h => hγ h.1]
    rw [h0]
    simp [sqX, V_of_not p _ hγ, JCx1.needs.hsVec_zero]

theorem ew_top_nonneg (p : KB.Pl P Wp Wq) (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (γ : C.LPt) :
    0 ≤ TBB.Ew p (fun _ => 1) H (P.r + 1) w γ := by
  rw [ew_top_eq]
  positivity

theorem sqX_sub (p : KB.Pl P Wp Wq) {Cb : ℝ} (hCb : KB.InDDplus2 P p.l0 p.T.base Cb p.Θ) {w : List C.Letter}
    (hw : KB.CutWord P p.l0 w) {H₁ H₂ : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} (h₁ : KB.CptCoef p.T.base H₁)
    (h₂ : KB.CptCoef p.T.base H₂) (γ : C.LPt) (i : SqIx P w) :
    sqX p (fun g => H₁ g - H₂ g) w γ i = sqX p H₁ w γ i - sqX p H₂ w γ i := by
  cases i with
  | none => exact PBN.vecV_sub _ _ _ _ h₁ h₂
  | some q =>
    obtain ⟨F₁, hF₁, hΘ₁, hV₁⟩ := theta_compact_support Wp Wq P p H₁ w q.1 Cb hCb h₁ hw
    obtain ⟨F₂, hF₂, hΘ₂, hV₂⟩ := theta_compact_support Wp Wq P p H₂ w q.1 Cb hCb h₂ hw
    obtain ⟨nf, fib, o, κ, Dop, -, hIn, -, -, hΘ⟩ := hCb w hw q.1
    have hlen : ∀ T ∈ Dop, T.word.length ≤ o := by
      intro T hT
      obtain ⟨_, _, _, _, _, _, _, hl, _⟩ := hIn.2.2 T hT
      omega
    have e : p.V (p.Θ.Θ w q.1 (fun g => H₁ g - H₂ g)) γ = p.V (fun g => F₁ g - F₂ g) γ := by
      refine PBE.vecV_congrGPos _ _ _ _ fun g hg => ?_
      have hg' : g ∈ C6.domL p.T.base ∅ := ⟨hg.1, hg.2, fun l hl => by simp at hl⟩
      rw [← hΘ₁ g hg', ← hΘ₂ g hg', hΘ _ g hg', hΘ _ g hg', hΘ _ g hg']
      exact PBE.opApply_subGV Dop hlen (B5.ckOn_mono le_top h₁.1) (B5.ckOn_mono le_top h₂.1) g hg.1
    simp only [sqX]
    rw [e, hV₁, hV₂, ← ContinuousLinearMap.comp_sub]
    congr 1
    exact PBN.vecV_sub _ _ _ _ hF₁ hF₂

theorem sqrt_sum_tri {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℂ E] (a : ι → ℝ)
    (x y : ι → E) :
    |Real.sqrt (∑ i, a i ^ 2 * ‖x i‖ ^ 2) - Real.sqrt (∑ i, a i ^ 2 * ‖y i‖ ^ 2)| ≤
      Real.sqrt (∑ i, a i ^ 2 * ‖x i - y i‖ ^ 2) := by
  have key : ∀ z : ι → E, Real.sqrt (∑ i, a i ^ 2 * ‖z i‖ ^ 2) =
      ‖(WithLp.toLp 2 fun i => (a i : ℂ) • z i : PiLp 2 fun _ : ι => E)‖ := by
    intro z
    rw [PiLp.norm_eq_of_L2]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [norm_smul, mul_pow]
  rw [key, key, key (fun i => x i - y i)]
  refine (abs_norm_sub_norm_le _ _).trans (le_of_eq ?_)
  congr 1
  ext i
  simp [smul_sub]

theorem topD_tri (p : KB.Pl P Wp Wq) {Cb : ℝ} (hCb : KB.InDDplus2 P p.l0 p.T.base Cb p.Θ) {w : List C.Letter}
    (hw : KB.CutWord P p.l0 w) {H₁ H₂ : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} (h₁ : KB.CptCoef p.T.base H₁)
    (h₂ : KB.CptCoef p.T.base H₂) (c : Fin (P.r + 1) → ℂ) :
    |Real.sqrt (topD p H₁ w c) - Real.sqrt (topD p H₂ w c)| ≤ Real.sqrt (topD p (fun g => H₁ g - H₂ g) w c) := by
  unfold topD
  rw [ew_top_eq, ew_top_eq, ew_top_eq]
  refine (sqrt_sum_tri _ _ _).trans (le_of_eq ?_)
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sqX_sub p hCb hw h₁ h₂]
  congr 3

theorem V_bigPt_aesm (p : KB.Pl P Wp Wq) {H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} (hH : KB.CptCoef p.T.base H) :
    AEStronglyMeasurable (fun c : Fin (P.r + 1) → ℂ => p.V H (TBB.bigPt P.r c)) volume := by
  obtain ⟨Φ0, hΦ, -, -, hV⟩ := phi_zero_hermitian_curvature Wp Wq P p H hH
  have hcont : Continuous (fun q : (Fin (P.r + 1) → ℂ) × U.XiH (P.r + 1) 0 1 =>
      U.psiH U.betaU 1 q.2 • Φ0 (U.ZjH (p := P.r + 1) (s := 0) 1 q.1 q.2 fun x => x.elim0)) := by
    have hZ : Continuous (fun q : (Fin (P.r + 1) → ℂ) × U.XiH (P.r + 1) 0 1 =>
        U.ZjH (p := P.r + 1) (s := 0) 1 q.1 q.2 fun x => x.elim0) := by
      have e : (fun q : (Fin (P.r + 1) → ℂ) × U.XiH (P.r + 1) 0 1 => U.ZjH (p := P.r + 1) (s := 0) 1 q.1 q.2 fun x => x.elim0) =
          fun q => U.headH 1 q.1 q.2.2.1 q.2.2.2 := funext fun q => PBM.zjH_eq 1 q.1 q.2
      rw [e]
      unfold U.headH
      exact ((continuous_const.matrix_mul ((Dx2.SL.cont_lowW 1).comp continuous_snd.snd.fst)).matrix_mul
        continuous_fst.matrix_diagonal).matrix_mul (Dx2.SL.cont_upper.comp continuous_snd.snd.snd)
    exact ((Ux13.continuous_psiH U.betaU 1).comp continuous_snd).smul (hΦ.continuous.comp hZ)
  have hm : StronglyMeasurable (fun c : Fin (P.r + 1) → ℂ =>
      U.PhiTop (p := P.r + 1) (s := 0) U.betaU 1 c Φ0 fun x => x.elim0) := by
    unfold U.PhiTop U.muXiH
    exact hcont.stronglyMeasurable.integral_prod_right'
  refine hm.aestronglyMeasurable.congr ?_
  filter_upwards [ae_coords_ne_zero (P.r + 1)] with c hc
  exact (hV _ 1 c (PBJ.Dens.isLocPt_bigPt c hc) (PBJ.Dens.ptMatN_bigPt c).symm).symm

theorem sqW_meas (p : KB.Pl P Wp Wq) (w : List C.Letter) (i : SqIx P w) :
    Measurable (fun c : Fin (P.r + 1) → ℂ => sqW p w (TBB.bigPt P.r c) i) := by
  have hn : Measurable (fun c : Fin (P.r + 1) → ℂ => TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c)) := by
    have e : (fun c : Fin (P.r + 1) → ℂ => TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c)) = fun c =>
        ∏ i : Fin (P.r + 1), (if 1 + (i : ℕ) = P.r + 1 then (Complex.normSq (c (Fin.last P.r)) - TBB.TTp p) ^ (P.k - 1)
          else ‖c i‖ ^ (2 * (C.Mlev P.k P.r (1 + (i : ℕ)) - 2))) := by
      funext c
      unfold TBB.nPt D.ptGG
      rw [ptLast_bigPt]
      unfold TBB.bigPt
      rw [level_product_of_constant_weights]
    rw [e]
    refine Finset.measurable_prod _ fun i _ => ?_
    split_ifs
    · exact ((Complex.continuous_normSq.measurable.comp (measurable_pi_apply _)).sub_const _).pow_const _
    · exact (measurable_pi_apply i).norm.pow_const _
  have hW : Measurable (fun c : Fin (P.r + 1) → ℂ => Top.wPt (TBB.TTp p) P.r (TBB.bigPt P.r c)) := by
    have e : (fun c : Fin (P.r + 1) → ℂ => Top.wPt (TBB.TTp p) P.r (TBB.bigPt P.r c)) = fun c =>
        Complex.normSq (∏ i, c i) / (Complex.normSq (∏ i, c i) -
          TBB.TTp p * Complex.normSq (∏ i : Fin P.r, c i.castSucc)) := by
      funext c
      show Top.wPt (TBB.TTp p) P.r (PBJ.bigPt c) = _
      unfold Top.wPt D.ptG
      rw [PBM.ptMatN_bigPt_head, PBJ.Dens.ptMatN_bigPt, PBM.hMat_one, Matrix.det_diagonal, Matrix.det_diagonal]
    rw [e]
    have h1 : Continuous fun c : Fin (P.r + 1) → ℂ => Complex.normSq (∏ i, c i) :=
      Complex.continuous_normSq.comp (continuous_finsetProd _ fun i _ => continuous_apply i)
    have h2 : Continuous fun c : Fin (P.r + 1) → ℂ => Complex.normSq (∏ i : Fin P.r, c i.castSucc) :=
      Complex.continuous_normSq.comp (continuous_finsetProd _ fun i _ => continuous_apply _)
    exact h1.measurable.div (h1.sub (continuous_const.mul h2)).measurable
  cases i with
  | none =>
    simp only [sqW]
    split_ifs
    · exact hn.sqrt
    · exact measurable_const
  | some q =>
    simp only [sqW]
    split_ifs
    · exact measurable_const
    · unfold Top.dH
      exact hn.sqrt.mul ((hW.pow_const _).mul_const _).sqrt

theorem sqX_aesm (p : KB.Pl P Wp Wq) {Cb : ℝ} (hCb : KB.InDDplus2 P p.l0 p.T.base Cb p.Θ) {w : List C.Letter}
    (hw : KB.CutWord P p.l0 w) {H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} (hH : KB.CptCoef p.T.base H) (i : SqIx P w) :
    AEStronglyMeasurable (fun c : Fin (P.r + 1) → ℂ => sqX p H w (TBB.bigPt P.r c) i) volume := by
  cases i with
  | none => exact V_bigPt_aesm p hH
  | some q =>
    obtain ⟨F, hF, -, hV⟩ := theta_compact_support Wp Wq P p H w q.1 Cb hCb hH hw
    simp only [sqX, hV]
    exact (continuous_const.clm_comp continuous_id).comp_aestronglyMeasurable (V_bigPt_aesm p hF)

theorem topD_aesm (p : KB.Pl P Wp Wq) {Cb : ℝ} (hCb : KB.InDDplus2 P p.l0 p.T.base Cb p.Θ) {w : List C.Letter}
    (hw : KB.CutWord P p.l0 w) {H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} (hH : KB.CptCoef p.T.base H) :
    AEStronglyMeasurable (topD p H w) volume := by
  have e : topD p H w = fun c => ∑ i : SqIx P w, sqW p w (TBB.bigPt P.r c) i ^ 2 *
      ‖B.hsVec (sqX p H w (TBB.bigPt P.r c) i)‖ ^ 2 := funext fun c => ew_top_eq p H w _
  rw [e]
  refine Finset.aestronglyMeasurable_fun_sum _ fun i _ => ?_
  exact ((sqW_meas p w i).pow_const 2).aestronglyMeasurable.mul
    ((BetaSesquilinearity.hsVec_cont.comp_aestronglyMeasurable (sqX_aesm p hCb hw hH i)).norm.pow 2)

end

end CompanionTheory.NFCpt
end

namespace CompanionTheory.NFCpt

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP Filter Topology MeasureTheory

noncomputable section

open Classical

theorem uInv_at_zero {X : Type} [AddCommGroup X] [Module ℂ X] :
    ∀ (w : List C.Letter) (x : Wd.Ix (Fin w.length) → X), KB.uInv 0 w x = x
  | [], _ => rfl
  | l :: w, x => by
    funext e
    simp only [KB.uInv, uInv_at_zero w, map_zero, ite_self, zero_smul, add_zero]
    split_ifs with h
    · congr 1
      funext a
      induction a using Fin.cases with
      | zero => exact h.symm
      | succ i => rfl
    · congr 1
      funext a
      induction a using Fin.cases with
      | zero =>
        have h1 : e (0 : Fin (w.length + 1)) = 1 := by
          rcases Fin.exists_fin_two.1 ⟨e (0 : Fin (w.length + 1)), rfl⟩ with h0 | h0
          · exact absurd h0 h
          · exact h0
        exact h1.symm
      | succ i => rfl

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem waveG_at_zero {k r : ℕ} (Bs : B.RealPlaceData k r Wp Wq) (w : List C.Letter)
    (x : Wd.Ix (Fin w.length) → B.Mat k r → (Wq →L[ℂ] Wp)) : KB.waveG Bs 0 w x = x := by
  funext e g
  simp [KB.waveG, P5.fsv, uInv_at_zero]

theorem ew_snoc (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) {j : ℕ} (hj : j ≤ P.r)
    {h : C.LPt} (hh : D.IsLocPt h j) (c : ℂ) :
    TBB.Ew p (fun _ => 1) F (j + 1) w (h ++ [(1, c)]) = C.nAux P.k P.r 0 (fun _ _ => 1) 1 h *
      ((KB.levW P (j + 1) c : ℂ) * p.RR F (j + 1) w (h ++ [(1, c)]) (h ++ [(1, c)])).re := by
  have hN : TBB.normC (fun _ => (1 : ℝ)) w = 1 := by simp [TBB.normC]
  set A := C.nAux P.k P.r 0 (fun _ _ => 1) 1 h with hAdef
  have hA : 0 ≤ A := PBD.lpt_value_nonneg_of_pos_of_size_le P.k P.r 0 (fun _ _ => 1) (fun _ _ => one_pos) h 1 le_rfl
    (by rw [hh.2]; omega)
  have hn : TBB.nPt P.k P.r (TBB.TTp p) (h ++ [(1, c)]) =
      A * C.nAux P.k P.r (D.ptGG (TBB.TTp p) (h ++ [(1, c)])) (fun _ _ => 1) (1 + j) [(1, c)] := by
    unfold TBB.nPt
    rw [PBD.weight_product_append, hh.2, hAdef, PBD.weight_product_indep_of_real_parameter P.k P.r _ 0 (fun _ _ => 1) h 1 le_rfl (by rw [hh.2]; omega)]
  unfold TBB.Ew TBB.NP
  rw [hn, hN, div_one, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  by_cases hjr : j = P.r
  · subst hjr
    by_cases hc2 : Complex.normSq c ≤ Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z'
    · have h0 : p.RR F (P.r + 1) w (h ++ [(1, c)]) (h ++ [(1, c)]) = 0 :=
        PBD.rrTop_zero P p.l0 p.T p.ν' p.m₀ p.Θ p.TP (M.sgn P p.l0) F w h _ c hh.2 hc2
      rw [h0]
      simp
    · push Not at hc2
      have hT : Tz P.k P.r p.T.base.z = P.T := p.hP.2.2.2.1
      have hT' : Tz P.k P.r p.T.base.z' = P.T' := p.hP.2.2.2.2.1
      have hlast : D.ptGG (TBB.TTp p) (h ++ [(1, c)]) = Complex.normSq c - TBB.TTp p := by
        simp [D.ptGG, D.ptLast]
      have hTT : TBB.TTp p = P.T * P.T' := by
        unfold TBB.TTp
        rw [hT, hT']
      have hfac : C.nAux P.k P.r (D.ptGG (TBB.TTp p) (h ++ [(1, c)])) (fun _ _ => 1) (1 + P.r) [(1, c)] =
          KB.levW P (P.r + 1) c := by
        rw [hlast, hTT]
        rw [hT, hT'] at hc2
        simp only [C.nAux, KB.levW, B2.zWeight, if_pos hc2.le]
        rw [if_pos ⟨by omega, trivial⟩]
        simp
      have hlev : 0 ≤ KB.levW P (P.r + 1) c := by
        rw [← hfac, hlast]
        simp only [C.nAux]
        rw [if_pos ⟨by omega, trivial⟩]
        have : 0 ≤ Complex.normSq c - TBB.TTp p := by
          unfold TBB.TTp; linarith
        simpa using pow_nonneg this _
      rw [hfac, Real.mul_self_sqrt (mul_nonneg hA hlev)]
      ring
  · have hfac : C.nAux P.k P.r (D.ptGG (TBB.TTp p) (h ++ [(1, c)])) (fun _ _ => 1) (1 + j) [(1, c)] =
        KB.levW P (j + 1) c := by
      simp only [C.nAux, KB.levW]
      rw [if_neg (by omega), if_neg (by omega)]
      have e : 1 + j + 1 - 1 = j + 1 := by omega
      rw [e]
      simp only [one_mul, mul_one, Nat.cast_one]
      congr 1
      ring
    have hlev : 0 ≤ KB.levW P (j + 1) c := by
      simp only [KB.levW]
      rw [if_neg (by omega)]
      exact zpow_nonneg (norm_nonneg _) _
    rw [hfac, Real.mul_self_sqrt (mul_nonneg hA hlev)]
    ring

theorem ew_low (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) {j : ℕ} (hj : j ≤ P.r)
    {h : C.LPt} (hh : D.IsLocPt h j) :
    TBB.Ew p (fun _ => 1) F j w h = C.nAux P.k P.r 0 (fun _ _ => 1) 1 h * (p.RR F j w h h).re := by
  have hN : TBB.normC (fun _ => (1 : ℝ)) w = 1 := by simp [TBB.normC]
  have hA := PBD.lpt_value_nonneg_of_pos_of_size_le P.k P.r 0 (fun _ _ => 1) (fun _ _ => one_pos) h 1 le_rfl (by rw [hh.2]; omega)
  unfold TBB.Ew TBB.NP TBB.nPt
  rw [hN, div_one, Complex.re_ofReal_mul,
    PBD.weight_product_indep_of_real_parameter P.k P.r _ 0 (fun _ _ => 1) h 1 le_rfl (by rw [hh.2]; omega), Real.mul_self_sqrt hA]

theorem ew_step (hPS : StandardPairingDecay.PStdC) (p : KB.Pl P Wp Wq) {Cb : ℝ} (hCb : KB.InDDplus2 P p.l0 p.T.base Cb p.Θ)
    {w : List C.Letter} (hw : KB.CutWord P p.l0 w) {F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)}
    (hF : KB.CptCoef p.T.base F) {j : ℕ} (hj : j ≤ P.r) {h : C.LPt} (hh : D.IsLocPt h j) :
    Integrable (fun c : ℂ => TBB.Ew p (fun _ => 1) F (j + 1) w (h ++ [(1, c)])) ∧
      ∫ c : ℂ, TBB.Ew p (fun _ => 1) F (j + 1) w (h ++ [(1, c)]) = TBB.Ew p (fun _ => 1) F j w h := by
  obtain ⟨φ, -, hφi, hφ, hint⟩ := hPS Wp Wq P p F j hj w h h hh hh Cb hCb hF hw
  have hae : (fun c : ℂ => C.nAux P.k P.r 0 (fun _ _ => 1) 1 h * (φ c).re) =ᵐ[volume]
      fun c : ℂ => TBB.Ew p (fun _ => 1) F (j + 1) w (h ++ [(1, c)]) := by
    filter_upwards [ae_ne_zero_c] with c hc
    rw [ew_snoc p F w hj hh c, hφ c hc]
  refine ⟨(hφi.re.const_mul _).congr hae, ?_⟩
  have h0 := hint 0
  rw [waveG_at_zero, ← PBL.rr_eq_form p F j hj w h h hh hh] at h0
  simp only [P5.fsv, zero_mul, map_zero, sub_self, Complex.exp_zero, one_mul] at h0
  rw [← integral_congr_ae hae, integral_const_mul, ew_low p F w hj hh, ← h0]
  congr 1
  exact integral_re hφi

theorem isLocPt_ofFn {j : ℕ} (c : Fin j → ℂ) (hc : ∀ a, c a ≠ 0) :
    D.IsLocPt (List.ofFn fun l => ((1 : ℕ), c l)) j := PBJ.Dens.isLocPt_bigPt c hc

theorem topForm_cpt (hPS : StandardPairingDecay.PStdC) (p : KB.Pl P Wp Wq) {Cb : ℝ} (hCb : KB.InDDplus2 P p.l0 p.T.base Cb p.Θ)
    {w : List C.Letter} (hw : KB.CutWord P p.l0 w) {F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)}
    (hF : KB.CptCoef p.T.base F) :
    Integrable (topD p F w) ∧ ∫ c, topD p F w c = (p.RR F 0 w [] []).re := by
  have h := tower_integral (P.r + 1)
    (fun j c => TBB.Ew p (fun _ => 1) F j w (List.ofFn fun l => ((1 : ℕ), c l)))
    (topD_aesm p hCb hw hF) (fun c _ => ew_top_nonneg p F w _) (fun j hj c hc => by
      have e : ∀ t : ℂ, (List.ofFn fun l : Fin (j + 1) => ((1 : ℕ), (Fin.snoc c t : Fin (j + 1) → ℂ) l)) =
          (List.ofFn fun l => ((1 : ℕ), c l)) ++ [(1, t)] := by
        intro t
        rw [List.ofFn_succ']
        simp [List.concat_eq_append]
      simp only [e]
      exact ew_step hPS p hCb hw hF (by omega) (isLocPt_ofFn c hc))
  refine ⟨h.1, h.2.trans ?_⟩
  simp only [List.ofFn_zero]
  rw [TBBx3.ew_zero_nil]
  simp [TBB.normC]

end

end CompanionTheory.NFCpt
end

namespace CompanionTheory.NFCpt

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP Filter Topology MeasureTheory

noncomputable section

open Classical

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def ordM (P : M.Par) (N : ℕ) : ℕ := 3 * (11 * (N * (2 * P.r + P.k + 1) ^ 2 + (2 * P.r + P.k + 1) ^ 3) + 5)

theorem residue_zero_bound : ∃ Cs : ℝ, 0 ≤ Cs ∧ ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (χ : ℝ → ℝ) (ε A : ℝ) (N : ℕ), C6.IsCut0 χ → 0 < ε →
    Cs * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A →
    ∀ w : List C.Letter, w.length ≤ N → ∃ K : ℝ, 0 ≤ K ∧
      ∀ (h : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (c : ℝ), B.CkOn ⊤ (B.GV P.k P.r) h → B.CCle A (ordM P N) h c →
        ‖p.RR (D.cutF p.T.base χ h ε) 0 w [] []‖ ≤ K * c ^ 2 := by
  obtain ⟨Cs, hCs0, hSQ⟩ := PBE.sliceQ
  refine ⟨Cs, hCs0, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p χ ε A N hχ hε hA w hw
  have hk2 : 2 ≤ P.k := p.hl.2.2
  have hloc : D.IsLocPt ([] : C.LPt) 0 := ⟨by simp, rfl⟩
  have hc : P.r - 0 = P.r - D.ptSize ([] : C.LPt) := rfl
  have hQ := fun e => hSQ Cs le_rfl P.k P.r Wp Wq p.T χ A N P rfl rfl hk2 hχ hA ε hε 0 (Nat.zero_le _) w hw [] hc
    hloc e
  choose εa Ka hεa hKa hQ1 _ using hQ
  set KK : ℝ := ∑ e, Ka e with hKK
  have hKa' : ∀ e, Ka e ≤ KK := fun e => Finset.single_le_sum (f := Ka) (fun e _ => hKa e) (Finset.mem_univ e)
  have hKK0 : 0 ≤ KK := Finset.sum_nonneg fun e _ => hKa e
  have hAu : P5.Auser P w.length + 1 ≤ P5.Auser P N + 1 := by linarith [PBE.auser_mono P hw]
  obtain ⟨Cf, hCf0, hCf⟩ := JCx4.formLev_bound_mm P p.T (M.sgn P p.l0) ⟨0, by omega⟩ w (P5.Auser P N + 1 + 1)
    (by linarith)
  have hmm5 : 5 + (2 * (P.r - 0) + P.k + 1) * w.length ≤ P5.mmUser P N := by
    have := JCx2.pd_thr_mm P ⟨0, by omega⟩ N (P5.mmUser P N) le_rfl
    have h2 : (2 * (P.r - 0) + P.k + 1) * w.length ≤ (2 * (P.r - 0) + P.k + 1) * N := Nat.mul_le_mul_left _ hw
    simp only at this
    omega
  have h5 : 5 ≤ P5.mmUser P N := by unfold P5.mmUser; omega
  refine ⟨Cf * KK ^ 2, by positivity, fun h c hh hcc => ?_⟩
  have hc0 : 0 ≤ c := JCx2.pd_ccle_nonneg hcc
  have hx : ∀ e, B.CCle (P5.Auser P N + 1) (P5.mmUser P N) (PBE.xs p.T χ ε 0 (Nat.zero_le _) w [] hc h e) (KK * c) :=
    fun e => JCx2.pd_ccle_mono_c (hQ1 e h c hh hcc).2 (mul_le_mul_of_nonneg_right (hKa' e) hc0)
  have hw0 : (0 : ℝ) ≤ w.length := Nat.cast_nonneg _
  have hb := hCf (PBE.xs p.T χ ε 0 (Nat.zero_le _) w [] hc h) (PBE.xs p.T χ ε 0 (Nat.zero_le _) w [] hc h)
    (KK * c) (KK * c) (fun e => BetaSesquilinearity.CCle_mono_A (by linarith) (BetaSesquilinearity.CCle_mono_m hmm5 (hx e)))
    (fun e => BetaSesquilinearity.CCle_mono_A (by linarith) (BetaSesquilinearity.CCle_mono_m h5 (hx e)))
  have e : p.RR (D.cutF p.T.base χ h ε) 0 w [] [] = D.formLev p.T (M.sgn P p.l0) ⟨0, by omega⟩ w
      (PBE.xs p.T χ ε 0 (Nat.zero_le _) w [] hc h) (PBE.xs p.T χ ε 0 (Nat.zero_le _) w [] hc h) := by
    unfold KB.Pl.RR D.RRplace
    rw [dite_eq_left ⟨hloc, hloc⟩, dite_eq_left (Nat.zero_le _)]
    rfl
  rw [e]
  exact hb.trans (le_of_eq (by ring))

theorem topForm_cut (hPS : StandardPairingDecay.PStdC) (Cb : ℝ) : ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ) (ε A : ℝ) (N : ℕ),
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → C6.IsCut0 χ → 0 < ε → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A m f) →
    Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A →
    ∀ w, KB.CutWord P p.l0 w → w.length ≤ N →
      Integrable (topD p (D.cutF p.T.base χ f ε) w) ∧
        ∫ c, topD p (D.cutF p.T.base χ f ε) w c = (p.RR (D.cutF p.T.base χ f ε) 0 w [] []).re := by
  obtain ⟨Cs, hCs0, hB⟩ := residue_zero_bound
  obtain ⟨Cl, hL⟩ := limit_of_module_forms Cb
  refine ⟨max (Cs + 1) Cl, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f χ ε A N hCb hχ hε hf hfA hA w hw hwN
  set X : ℝ := (N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3 with hX
  have hX1 : 1 ≤ X := by
    have h1 : (1 : ℝ) ≤ 2 * (P.r : ℝ) + P.k + 1 := by
      have : (0 : ℝ) ≤ P.r := Nat.cast_nonneg _
      have : (0 : ℝ) ≤ P.k := Nat.cast_nonneg _
      linarith
    have : 1 ≤ (2 * (P.r : ℝ) + P.k + 1) ^ 3 := one_le_pow₀ h1
    have : 0 ≤ (N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 := by positivity
    linarith
  have hR4 : 1 ≤ ((P.r : ℝ) + 1) ^ 4 := one_le_pow₀ (by have : (0 : ℝ) ≤ P.r := Nat.cast_nonneg _; linarith)
  have hmono : ∀ c, c ≤ max (Cs + 1) Cl → c * ((P.r : ℝ) + 1) ^ 4 * X ≤ A := fun c hc =>
    le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (by positivity)) (by positivity)) hA
  have hA' : Cs * ((P.r : ℝ) + 1) ^ 4 * X ≤ A - 1 := by
    have h1 := hmono _ (le_max_left _ _)
    have h2 : 1 ≤ ((P.r : ℝ) + 1) ^ 4 * X := by nlinarith
    nlinarith
  obtain ⟨hcpt, hlim⟩ := hL Wp Wq P p f χ ε A N (cutN P.k P.r) hCb hχ hε hf hfA (hmono _ (le_max_right _ _))
    (fun _ _ => rfl)
  obtain ⟨K, hK0, hK⟩ := hB Wp Wq P p χ ε (A - 1) N hχ hε hA' w hwN
  obtain ⟨bf, hbf⟩ := hfA (ordM P N)
  have hbf0 : 0 ≤ bf := JCx2.pd_ccle_nonneg hbf
  obtain ⟨Kp, hKp0, hKp⟩ := JCx2.pd_cut_ccle (k := P.k) (r := P.r) (E := Wq →L[ℂ] Wp) (ordM P N)
  have hψ : ∀ n : ℕ, B.CCle (A - 1) (ordM P N) (fun g => JCx2.pdPsi ((n : ℝ) + 1) g • f g)
      (Kp * bf / ((n : ℝ) + 1)) := fun n => hKp _ (by positivity) A f bf hbf
  have hψs : ∀ n : ℕ, B.CkOn ⊤ (B.GV P.k P.r) (fun g => JCx2.pdPsi ((n : ℝ) + 1) g • f g) :=
    fun n => JCx2.pd_smooth_smul (JCx2.pd_psi_cd _) hf
  set H : ℕ → B.Mat P.k P.r → (Wq →L[ℂ] Wp) := fun n g => cutN P.k P.r n g • D.cutF p.T.base χ f ε g with hH
  have hdiff : ∀ n m : ℕ, (fun g => H n g - H m g) = D.cutF p.T.base χ
      (fun g => JCx2.pdPsi ((m : ℝ) + 1) g • f g + (-1 : ℂ) • (JCx2.pdPsi ((n : ℝ) + 1) g • f g)) ε := by
    intro n m
    funext g
    simp only [hH, D.cutF, PBE.cut_eq (cutN P.k P.r) (fun _ _ => rfl)]
    module
  have hdc : ∀ n m, KB.CptCoef p.T.base (fun g => H n g - H m g) := fun n m => PBN.cpt_sub _ (hcpt n) (hcpt m)
  have hd : ∀ n m : ℕ, ∫ c, topD p (fun g => H n g - H m g) w c ≤
      K * (Kp * bf / ((m : ℝ) + 1) + Kp * bf / ((n : ℝ) + 1)) ^ 2 := by
    intro n m
    rw [(topForm_cpt hPS p hCb hw (hdc n m)).2, hdiff]
    refine (Complex.re_le_norm _).trans (hK _ _ (BetaSesquilinearity.CkOn_add (hψs m) (BetaSesquilinearity.CkOn_smul (-1) (hψs n))) ?_)
    have := BetaSesquilinearity.CCle_add (hψ m) (BetaSesquilinearity.CCle_smul (-1) (hψ n))
    simpa using this
  refine integral_eq_of_sqrt_cauchy (q := fun n => topD p (H n) w) (d := fun n m => topD p (fun g => H n g - H m g) w)
    (fun n => (topForm_cpt hPS p hCb hw (hcpt n)).1) (fun n c => ew_top_nonneg p _ w _)
    (fun n m => (topForm_cpt hPS p hCb hw (hdc n m)).1) (fun n m c => ew_top_nonneg p _ w _)
    (fun n m c => topD_tri p hCb hw (hcpt n) (hcpt m) c) (Eventually.of_forall fun c => ?_) ?_ ?_
  · unfold topD TBB.Ew TBB.NP
    exact (Complex.continuous_re.tendsto _).comp ((hlim (P.r + 1) w hw hwN _ _).const_mul _)
  · exact ((Complex.continuous_re.tendsto _).comp (hlim 0 w hw hwN [] [])).congr
      fun n => (topForm_cpt hPS p hCb hw (hcpt n)).2.symm
  · intro η hη
    have h1 : Tendsto (fun n : ℕ => K * (2 * (Kp * bf / ((n : ℝ) + 1))) ^ 2) atTop (𝓝 0) := by
      have h0 : Tendsto (fun n : ℕ => Kp * bf / ((n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
      simpa using ((h0.const_mul 2).pow 2).const_mul K
    obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (h1.eventually (ge_mem_nhds hη))
    refine ⟨N₀, fun n m hn hm => (hd n m).trans (le_trans ?_ (hN₀ N₀ le_rfl))⟩
    have hb : ∀ j : ℕ, N₀ ≤ j → Kp * bf / ((j : ℝ) + 1) ≤ Kp * bf / ((N₀ : ℝ) + 1) := fun j hj =>
      div_le_div_of_nonneg_left (by positivity) (by positivity) (by exact_mod_cast Nat.succ_le_succ hj)
    refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ 2) hK0
    linarith [hb n hn, hb m hm]

def NFTopFormAllCpt : Prop :=
  P5.ThmPActualCpt → ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A₀ : ℝ) (p₀ : ℕ) (χ : ℝ → ℝ) (Y : Finset ℝ) (N : ℕ),
    NFHyp Cb Cc p f A₀ p₀ χ N → ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N →
      NFTopForm p χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) w

theorem top_form_all_compact : NFTopFormAllCpt := by
  intro hA Cb
  obtain ⟨Cc, hC⟩ := topForm_cut (StandardPairingDecay.pStdC_of hA radial_head head_top) Cb
  refine ⟨Cc, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f A₀ p₀ χ Y N hH w hw hN ε hε
  obtain ⟨hχ, hCb, hf, hfA, hth, -⟩ := hH
  have hid : B.CkOn ⊤ (B.GV P.k P.r) (fun _ : B.Mat P.k P.r => ContinuousLinearMap.id ℂ Wq) := fun g₀ _ =>
    ⟨Set.univ, fun _ => ContinuousLinearMap.id ℂ Wq, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩
  exact (hC Wp Wq P p _ χ ε _ N hCb hχ hε (ckOn_fpm p p₀ hf hid) (inCC_fpm_id p p₀ hfA) hth w hw.1 hN).2.symm

end

end CompanionTheory.NFCpt
