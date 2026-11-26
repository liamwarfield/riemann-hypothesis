module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicFrameOrbitLiftOfArcStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicFrameOrbitUnipotentOrderTwo
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicDescentPunctPolydiscLogCover
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DerivativesSeparateLieBasisCoeffsCartesian
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnKeySectionComplexValue
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsThetaPtStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCommonDenominatorIsIntegral
open ReciprocityTheory.ChartRestriction.G.FD NumberField

namespace GlobalTheory

theorem exists_common_denominator (E : Type) [Field E] [NumberField E] (n : ℕ) (f : Fin n → E) :
    ∃ d : ℕ, 0 < d ∧ ∀ j, IsIntegral ℤ ((d : E) * f j) := by
  classical
  obtain ⟨y, hy, h⟩ := exists_integral_multiples ℤ ℚ (L := E) (Finset.univ.image f)
  refine ⟨y.natAbs, Int.natAbs_pos.mpr hy, fun j => ?_⟩
  have hj := h (f j) (Finset.mem_image_of_mem f (Finset.mem_univ j))
  rw [zsmul_eq_mul] at hj
  rcases Int.natAbs_eq y with e | e
  · have : ((y.natAbs : ℕ) : E) = (y : E) := by
      conv_rhs => rw [e]
      simp
    rw [this]; exact hj
  · have : ((y.natAbs : ℕ) : E) = -(y : E) := by
      conv_rhs => rw [e]
      simp
    rw [this, neg_mul]; exact hj.neg

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CuspPnormLeExpNegOfIsIsoStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CuspPnormLeExpNegOfIsIso
open NumberField Complex Filter ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate Topology Real

namespace GlobalTheory

theorem cusp_pnorm_le_exp_neg_of_isIso (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (v : Fin r → E) (hP : P ∈ X.SS la)
    (hξ : X.IsIso v) :
    ∃ C c : ℝ, 0 < c ∧ ∀ x ∈ X.dom, ∀ t : ℝ, 1 ≤ t → (∀ τ, t ≤ X.tt v x τ) →
      X.pnorm la P x ≤ C * Real.exp (-c * t) := by
  obtain ⟨M, hM, htrans⟩ := HalfMax.exists_period X la
  obtain ⟨C0, hC0⟩ := hP.1.2
  set w : ℝ := ∑ τ, X.spread la τ with hw
  have hpi := Real.pi_pos
  refine ⟨2 ^ (w / 2) * C0, π / M, by positivity, fun z0 hz0 t' ht' htt' => ?_⟩
  obtain ⟨hv, hvv, hv0⟩ := id hξ
  set e : X.Ψ → Fin r → ℂ := fun τ => Data.emb τ.1 v with he
  have he0 : ∀ τ : X.Ψ, e τ ≠ 0 := by
    intro τ h
    apply hv0
    funext a
    have := congr_fun h a
    simpa [e, Data.emb] using this
  have heIso : X.IsIsoV e := fun τ => ⟨by
    show hermC τ.1 X.Gm (fun a => τ.1 (v a)) (fun a => τ.1 (v a)) = 0
    rw [EmbeddingHermitianPairs.hermC_emb, hvv, map_zero], he0 τ⟩
  set t : ℝ := t' / 2 with ht
  have ht0 : 0 < t := by linarith
  have htt : ∀ τ, 2 * t ≤ X.ttV e z0 τ := by
    intro τ
    have h : t' ≤ X.ttV e z0 τ := htt' τ
    linarith
  have hfl : ∀ s, X.flowV e s z0 = X.flow v s z0 := fun s => rfl
  have hdom : ∀ ζ : ℂ, -(2 * t) < ζ.im → X.flow v (fun _ => ζ) z0 ∈ X.dom := by
    intro ζ hζ
    rw [← hfl]
    refine ((flowDomainCriterion_holds r X e heIso z0 hz0 (fun _ => ζ)).1).2 (fun τ => ?_)
    show 0 < 1 + ζ.im / X.ttV e z0 τ
    have h := htt τ
    have hpos' : 0 < X.ttV e z0 τ := by linarith
    have : -1 < ζ.im / X.ttV e z0 τ := by rw [lt_div_iff₀ hpos']; linarith
    linarith
  set g : ℂ → ℂ := fun ζ => if -(2 * t) < ζ.im then P (X.flow v (fun _ => ζ) z0) else 0 with hg
  obtain ⟨γ, hγ, hχ, hγm⟩ := htrans v hv hvv
  have hper : Function.Periodic g M := by
    intro ζ
    simp only [hg, Complex.add_im, Complex.ofReal_im, add_zero]
    split_ifs with h
    · have hy := hdom ζ h
      have hlact : X.flow v (fun _ => ζ + (M : ℂ)) z0 = lact γ (X.flow v (fun _ => ζ) z0) := by
        funext τ
        show X.flowMat v τ (ζ + M) * mat z0 τ =
          (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat (X.flow v (fun _ => ζ) z0) τ
        rw [AdmissibleHermitianColumns.mat_flow, hγm τ, ← Matrix.mul_assoc,
          EmbeddingHermitianPairs.flowMat_mul X hvv, add_comm]
      rw [hlact, hP.1.1.2.2 γ hγ _ hy, hχ, one_mul]
    · rfl
  have hopen := FourierCoefficientDomain.isOpen_dom X
  have hdiff : ∀ ζ : ℂ, -(2 * t) < ζ.im → DifferentiableAt ℂ g ζ := by
    intro ζ hζ
    have hev : g =ᶠ[𝓝 ζ] fun ζ => P (X.flow v (fun _ => ζ) z0) := by
      have : {ζ : ℂ | -(2 * t) < ζ.im} ∈ 𝓝 ζ :=
        (isOpen_lt continuous_const Complex.continuous_im).mem_nhds hζ
      filter_upwards [this] with ζ' h'
      simp only [hg, if_pos (show -(2 * t) < ζ'.im from h')]
    refine DifferentiableAt.congr_of_eventuallyEq ?_ hev
    have hF : DifferentiableAt ℂ (fun ζ : ℂ => X.flow v (fun _ => ζ) z0) ζ :=
      ((FlowMeanContinuity.flow_differentiable X v z0).comp
        (differentiable_pi.2 fun _ => differentiable_id)) ζ
    exact (hP.1.1.1.differentiableAt (hopen.mem_nhds (hdom ζ hζ))).comp ζ hF
  have hzero : Tendsto g (comap im atTop) (𝓝 0) :=
    HalfMax.tendsto_zero X la P hP hz0 hξ
      (fun ζ hζ => hdom ζ (by linarith)) g
      (fun ζ hζ => by simp only [hg, if_pos (show -(2 * t) < ζ.im by linarith)])
  have hnz : 0 < X.nfac la z0 := flowTermNormDecay.nfac_pos X la hz0
  set B : ℝ := 2 ^ (w / 2) * C0 / X.nfac la z0 with hB
  have hBd : ∀ ζ : ℂ, ζ.im = -t → ‖g ζ‖ ≤ B := by
    intro ζ hζ
    have hlt : -(2 * t) < ζ.im := by linarith
    simp only [hg, if_pos hlt]
    set y := X.flow v (fun _ => ζ) z0 with hy
    have hyd := hdom ζ hlt
    have hnf : 0 < X.nfac la y := flowTermNormDecay.nfac_pos X la hyd
    have hratio : X.nfac la z0 / X.nfac la y ≤
        ∏ τ : X.Ψ, (max (1 + ζ.im / X.ttV e z0 τ) (1 + ζ.im / X.ttV e z0 τ)⁻¹) ^
          (X.spread la τ / 2) :=
      (m3bNorm_holds r X e heIso la z0 hz0 (fun _ => ζ) (by rw [hfl]; exact hyd)).2
    have hprod : ∏ τ : X.Ψ, (max (1 + ζ.im / X.ttV e z0 τ) (1 + ζ.im / X.ttV e z0 τ)⁻¹) ^
        (X.spread la τ / 2) ≤ (2 : ℝ) ^ (w / 2) := by
      have hterm : ∀ τ : X.Ψ, (max (1 + ζ.im / X.ttV e z0 τ) (1 + ζ.im / X.ttV e z0 τ)⁻¹) ^
          (X.spread la τ / 2) ≤ (2 : ℝ) ^ (X.spread la τ / 2) := by
        intro τ
        have h := htt τ
        have hT : 0 < X.ttV e z0 τ := by linarith
        have hq1 : 1 / 2 ≤ 1 + ζ.im / X.ttV e z0 τ := by
          rw [hζ, neg_div]
          have : t / X.ttV e z0 τ ≤ 1 / 2 := by rw [div_le_iff₀ hT]; linarith
          linarith
        have hq2 : 1 + ζ.im / X.ttV e z0 τ ≤ 1 := by
          rw [hζ, neg_div]
          have : 0 ≤ t / X.ttV e z0 τ := by positivity
          linarith
        have hqpos : 0 < 1 + ζ.im / X.ttV e z0 τ := by linarith
        have hinv : (1 + ζ.im / X.ttV e z0 τ)⁻¹ ≤ 2 := by
          rw [inv_le_comm₀ hqpos two_pos]
          linarith
        have hsp := flowTermNormDecay.spread_nonneg' X la τ
        exact Real.rpow_le_rpow (le_trans hqpos.le (le_max_left _ _))
          (max_le (by linarith) hinv) (by linarith)
      calc _ ≤ ∏ τ : X.Ψ, (2 : ℝ) ^ (X.spread la τ / 2) :=
            Finset.prod_le_prod₀ (fun τ _ => Real.rpow_nonneg (le_trans (by
              have h := htt τ
              have hT : 0 < X.ttV e z0 τ := by linarith
              have : t / X.ttV e z0 τ ≤ 1 / 2 := by rw [div_le_iff₀ hT]; linarith
              rw [hζ, neg_div]
              linarith) (le_max_left _ _)) _) (fun τ _ => hterm τ)
        _ = (2 : ℝ) ^ (∑ τ : X.Ψ, X.spread la τ / 2) := (Real.rpow_sum_of_pos two_pos _ _).symm
        _ = (2 : ℝ) ^ (w / 2) := by rw [← Finset.sum_div]
    have h1 : ‖P y‖ * X.nfac la y ≤ C0 := hC0 y hyd
    have h2 : X.nfac la z0 ≤ 2 ^ (w / 2) * X.nfac la y := by
      rw [div_le_iff₀ hnf] at hratio
      exact hratio.trans (mul_le_mul_of_nonneg_right hprod hnf.le)
    rw [hB, le_div_iff₀ hnz]
    calc ‖P y‖ * X.nfac la z0 ≤ ‖P y‖ * (2 ^ (w / 2) * X.nfac la y) := by gcongr
      _ = 2 ^ (w / 2) * (‖P y‖ * X.nfac la y) := by ring
      _ ≤ 2 ^ (w / 2) * C0 := by gcongr
  have hsch := PeriodicSchwarzLemma.periodic_schwarz hM ht0 (show t < 2 * t by linarith) hper hdiff hzero hBd
  have hg0 : g 0 = P z0 := by
    simp only [hg, Complex.zero_im, if_pos (show -(2 * t) < (0 : ℝ) by linarith)]
    congr 1
    exact EmbeddingHermitianPairs.flow_zero X v z0
  rw [hg0] at hsch
  have hexp : -2 * π * t / M = -(π / M) * t' := by
    rw [ht]
    ring
  rw [hexp, hB, ← mul_div_assoc, le_div_iff₀ hnz] at hsch
  calc X.pnorm la P z0 = ‖P z0‖ * X.nfac la z0 := rfl
    _ ≤ _ := hsch
    _ = _ := mul_comm _ _

end GlobalTheory
end

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pnorm_le_exp_neg_of_mem_SS_of_isIso : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (X : Data E N) (la : Wt X.Ψ N) (P : Frame X.Ψ N → ℂ) (ξ : Fin N → E), P ∈ X.SS la → X.IsIso ξ → ∃ C c : ℝ, 0 < c ∧ ∀ x ∈ X.dom, ∀ t : ℝ, 1 ≤ t → (∀ τ, t ≤ X.tt ξ x τ) → X.pnorm la P x ≤ C * Real.exp (-c * t) := by
  first | exact @GlobalTheory.cusp_pnorm_le_exp_neg_of_isIso | exact GlobalTheory.cusp_pnorm_le_exp_neg_of_isIso | (intros; apply GlobalTheory.cusp_pnorm_le_exp_neg_of_isIso <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrivialMonodromyOrbitConvergesSymmetricDomain
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrivialMonodromyOrbitConvergesSymmetricDomain
open GlobalTheory.ShFam.BdArc Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.ShFam.OrbitLimit

theorem eventually_imTop (T : ℝ) : ∀ᶠ w in imTop, T < w.im :=
  (tendsto_comap (f := Complex.im) (x := atTop)).eventually (eventually_gt_atTop T)

instance imTop_neBot : imTop.NeBot :=
  comap_neBot fun t ht => by
    obtain ⟨y, hy⟩ := Filter.nonempty_of_mem ht
    exact ⟨y * Complex.I, by simpa using hy⟩

theorem exists_tendsto_norm_lt {T h c : ℝ} (hh : 0 < h) {f : ℂ → ℂ} (hd : DifferentiableOn ℂ f {w | T < w.im})
    (hp : ∀ w : ℂ, T < w.im → f (w + h) = f w) (hb : ∀ w : ℂ, T < w.im → ‖f w‖ < c) :
    ∃ L, Tendsto f imTop (𝓝 L) ∧ ‖L‖ < c := by
  classical
  let g : ℂ → ℂ := fun w => if T < w.im then f w else 0
  have hg : ∀ w : ℂ, T < w.im → g w = f w := fun w hw => if_pos hw
  have hgp : Function.Periodic g h := fun w => by
    by_cases hw : T < w.im
    · rw [hg w hw, hg _ (by simpa using hw), hp w hw]
    · simp [g, hw]
  have ho : IsOpen {w : ℂ | T < w.im} := isOpen_lt continuous_const Complex.continuous_im
  have hgd : ∀ w : ℂ, T < w.im → DifferentiableAt ℂ g w := fun w hw =>
    (hd.congr fun z hz => hg z hz).differentiableAt (ho.mem_nhds hw)
  have hhol : ∀ᶠ w in imTop, DifferentiableAt ℂ g w := (eventually_imTop T).mono hgd
  have hbd : BoundedAtFilter imTop g := by
    refine Asymptotics.IsBigO.of_bound c ((eventually_imTop T).mono fun w hw => ?_)
    rw [hg w hw]
    simpa using (hb w hw).le
  set F := Function.Periodic.cuspFunction h g with hF
  set r : ℝ := Real.exp (-2 * Real.pi * (T + 1) / h) with hr
  have hr0 : 0 < r := Real.exp_pos _
  have him : ∀ q : ℂ, q ≠ 0 → ‖q‖ ≤ r → T < (Function.Periodic.invQParam h q).im := fun q hq hqr => by
    rw [← Function.Periodic.norm_qParam_lt_iff hh, Function.Periodic.qParam_right_inv hh.ne' hq]
    refine hqr.trans_lt (Real.exp_lt_exp.2 ?_)
    rw [div_lt_div_iff_of_pos_right hh]
    nlinarith [Real.pi_pos]
  have hFd : DifferentiableOn ℂ F (closure (Metric.ball 0 r)) := fun q hq => by
    rw [closure_ball _ hr0.ne', mem_closedBall_zero_iff] at hq
    refine DifferentiableAt.differentiableWithinAt ?_
    by_cases hq0 : q = 0
    · rw [hq0]
      exact Function.Periodic.differentiableAt_cuspFunction_zero hh hgp hhol hbd
    · rw [← Function.Periodic.qParam_right_inv hh.ne' hq0]
      exact Function.Periodic.differentiableAt_cuspFunction hh.ne' hgp (hgd _ (him q hq0 hq))
  refine ⟨F 0, (Function.Periodic.tendsto_at_I_inf hh hgp hhol hbd).congr' ((eventually_imTop T).mono hg), ?_⟩
  obtain ⟨z, hz, hmax⟩ := Complex.exists_mem_frontier_isMaxOn_norm (f := F) Metric.isBounded_ball
    (Metric.nonempty_ball.2 hr0) hFd.diffContOnCl
  rw [frontier_ball _ hr0.ne', mem_sphere_zero_iff_norm] at hz
  have hz0 : z ≠ 0 := fun h0 => by simp [h0] at hz; exact hr0.ne hz
  have h1 : ‖F 0‖ ≤ ‖F z‖ := hmax (subset_closure (Metric.mem_ball_self hr0))
  refine h1.trans_lt ?_
  rw [hF, Function.Periodic.cuspFunction_eq_of_nonzero _ _ hz0, hg _ (him z hz0 hz.le)]
  exact hb _ (him z hz0 hz.le)

def nsq {n : ℕ} (u : Fin n → ℂ) : ℝ := ∑ a, ‖u a‖ ^ 2

theorem nsq_nonneg {n : ℕ} (u : Fin n → ℂ) : 0 ≤ nsq u := Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem nsq_lim_lt {n : ℕ} {T h c : ℝ} (hh : 0 < h) {u : ℂ → Fin n → ℂ}
    (hd : ∀ a, DifferentiableOn ℂ (fun w => u w a) {w | T < w.im})
    (hp : ∀ w : ℂ, T < w.im → u (w + h) = u w) (hb : ∀ w : ℂ, T < w.im → nsq (u w) < c) {L : Fin n → ℂ}
    (hL : ∀ a, Tendsto (fun w => u w a) imTop (𝓝 (L a))) : nsq L < c := by
  obtain ⟨l, hl, hlt⟩ := exists_tendsto_norm_lt (c := (nsq L + c) / 2) hh
    (f := fun w => ∑ a, (starRingEnd ℂ) (L a) * u w a)
    (DifferentiableOn.fun_sum fun a _ => (hd a).const_mul _) (fun w hw => by simp only [hp w hw]) fun w hw => by
      refine (norm_sum_le _ _).trans_lt (lt_of_le_of_lt (b := (nsq L + nsq (u w)) / 2) ?_ (by linarith [hb w hw]))
      rw [nsq, nsq, ← Finset.sum_add_distrib, Finset.sum_div]
      refine Finset.sum_le_sum fun a _ => ?_
      rw [norm_mul, Complex.norm_conj]
      nlinarith [sq_nonneg (‖L a‖ - ‖u w a‖)]
  have h2 := tendsto_nhds_unique hl (tendsto_finsetSum _ fun a _ => (hL a).const_mul ((starRingEnd ℂ) (L a)))
  have h3 : l = (nsq L : ℝ) := by
    rw [h2, nsq]
    push_cast
    exact Finset.sum_congr rfl fun a _ => Complex.conj_mul' _
  rw [h3, Complex.norm_real, Real.norm_of_nonneg (nsq_nonneg L)] at hlt
  linarith

def Jm (N p : ℕ) : Matrix (Fin N) (Fin N) ℂ := diagonal fun a : Fin N => ((sgn p (a : ℕ) : ℝ) : ℂ)

theorem sum_castLE {N p : ℕ} (hp : p ≤ N) {R : Type} [AddCommMonoid R] (f : Fin N → R) :
    ∑ j, f (Fin.castLE hp j) = ∑ a : Fin N, if (a : ℕ) < p then f a else 0 := by
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun j _ => Fin.castLE hp j) (fun j _ => by simp) (fun a _ b _ h => Fin.castLE_injective hp h)
    (fun a ha => ⟨⟨a, by simpa using ha⟩, Finset.mem_univ _, rfl⟩) fun _ _ => rfl

theorem form_eq {N p : ℕ} (hp : p ≤ N) (u : Fin N → ℂ) :
    star u ⬝ᵥ Jm N p *ᵥ u = ((2 * nsq (fun j => u (Fin.castLE hp j)) - nsq u : ℝ) : ℂ) := by
  rw [nsq, nsq, sum_castLE hp (fun a => ‖u a‖ ^ 2), Finset.mul_sum, ← Finset.sum_sub_distrib, Complex.ofReal_sum,
    dotProduct]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Jm, mulVec_diagonal, mul_left_comm, Pi.star_apply, Complex.star_def, Complex.conj_mul', sgn]
  split_ifs <;> push_cast <;> ring

theorem posDef_iff {N p : ℕ} (hp : p ≤ N) (U : Matrix (Fin N) (Fin p) ℂ) :
    (Uᴴ * Jm N p * U).PosDef ↔
      ∀ v, v ≠ 0 → nsq (U *ᵥ v) < 2 * nsq (U.submatrix (Fin.castLE hp) id *ᵥ v) := by
  have hH : (Uᴴ * Jm N p * U).IsHermitian := by
    refine isHermitian_conjTranspose_mul_mul _ ?_
    rw [Jm, IsHermitian, diagonal_conjTranspose]
    congr 1
    funext a
    simp [Pi.star_apply]
  have key : ∀ v, star v ⬝ᵥ (Uᴴ * Jm N p * U) *ᵥ v =
      ((2 * nsq (U.submatrix (Fin.castLE hp) id *ᵥ v) - nsq (U *ᵥ v) : ℝ) : ℂ) := fun v => by
    rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec, form_eq hp]
    rfl
  rw [posDef_iff_dotProduct_mulVec, and_iff_right hH]
  refine forall_congr' fun v => forall_congr' fun _ => ?_
  rw [key, Complex.zero_lt_real, sub_pos]

theorem det_top_ne {N p : ℕ} (hp : p ≤ N) {U : Matrix (Fin N) (Fin p) ℂ} (hU : (Uᴴ * Jm N p * U).PosDef) :
    (U.submatrix (Fin.castLE hp) id).det ≠ 0 := fun h0 => by
  obtain ⟨v, hv, h1⟩ := exists_mulVec_eq_zero_iff.2 h0
  have h2 := (posDef_iff hp U).1 hU v hv
  rw [h1] at h2
  have h3 := nsq_nonneg (U *ᵥ v)
  simp [nsq] at h2 h3
  linarith

def IsGraph {N p : ℕ} (hp : p ≤ N) (Y : Matrix (Fin N) (Fin p) ℂ) : Prop :=
  Y.submatrix (Fin.castLE hp) id = 1 ∧ (Yᴴ * Jm N p * Y).PosDef

theorem IsGraph.nsq_lt {N p : ℕ} {hp : p ≤ N} {Y : Matrix (Fin N) (Fin p) ℂ} (h : IsGraph hp Y) {v : Fin p → ℂ}
    (hv : v ≠ 0) : nsq (Y *ᵥ v) < 2 * nsq v := by
  have := (posDef_iff hp Y).1 h.2 v hv
  rwa [h.1, one_mulVec] at this

theorem isGraph_mul_inv {N p : ℕ} (hp : p ≤ N) {U : Matrix (Fin N) (Fin p) ℂ} (hU : (Uᴴ * Jm N p * U).PosDef) :
    IsGraph hp (U * (U.submatrix (Fin.castLE hp) id)⁻¹) := by
  have hd := (det_top_ne hp hU).isUnit
  refine ⟨?_, ?_⟩
  · rw [← mul_nonsing_inv _ hd]
    rfl
  · have := hU.conjTranspose_mul_mul_same (B := (U.submatrix (Fin.castLE hp) id)⁻¹)
      (mulVec_injective_of_isUnit ((isUnit_iff_isUnit_det _).2 (isUnit_nonsing_inv_det _ hd)))
    simpa only [conjTranspose_mul, Matrix.mul_assoc] using this

theorem graph_limit {N p : ℕ} (hp : p ≤ N) {T h : ℝ} (hh : 0 < h) {Y : ℂ → Matrix (Fin N) (Fin p) ℂ}
    (hd : ∀ a j, DifferentiableOn ℂ (fun w => Y w a j) {w | T < w.im})
    (hper : ∀ w : ℂ, T < w.im → Y (w + h) = Y w) (hG : ∀ w : ℂ, T < w.im → IsGraph hp (Y w)) :
    ∃ Y₀, IsGraph hp Y₀ ∧ ∀ a j, Tendsto (fun w => Y w a j) imTop (𝓝 (Y₀ a j)) := by
  have hex : ∀ a j, ∃ L, Tendsto (fun w => Y w a j) imTop (𝓝 L) := fun a j => by
    obtain ⟨L, hL, -⟩ := exists_tendsto_norm_lt (c := 2) hh (hd a j) (fun w hw => by simp only [hper w hw])
      fun w hw => by
        have h1 := (hG w hw).nsq_lt (v := Pi.single j 1) (by simp)
        have h2 : nsq (Pi.single j (1 : ℂ) : Fin p → ℂ) = 1 := by
          rw [nsq, Finset.sum_eq_single j] <;> simp +contextual
        have h3 : ‖Y w a j‖ ^ 2 ≤ nsq (Y w *ᵥ Pi.single j 1) := by
          have := Finset.single_le_sum (f := fun a => ‖(Y w *ᵥ Pi.single j 1) a‖ ^ 2)
            (fun _ _ => sq_nonneg _) (Finset.mem_univ a)
          simpa [nsq] using this
        nlinarith [norm_nonneg (Y w a j)]
    exact ⟨L, hL⟩
  choose Y₀ hY using hex
  have h1 : (Matrix.of Y₀).submatrix (Fin.castLE hp) id = 1 := by
    ext i j
    refine tendsto_nhds_unique (hY (Fin.castLE hp i) j) (tendsto_const_nhds.congr' ((eventually_imTop T).mono ?_))
    intro w hw
    exact (congrFun (congrFun (hG w hw).1 i) j).symm
  refine ⟨Matrix.of Y₀, ⟨h1, (posDef_iff hp _).2 fun v hv => ?_⟩, hY⟩
  rw [h1, one_mulVec]
  refine nsq_lim_lt (T := T) hh (u := fun w => Y w *ᵥ v) (fun a => ?_) (fun w hw => by simp only [hper w hw])
    (fun w hw => (hG w hw).nsq_lt hv) fun a => ?_
  · exact DifferentiableOn.fun_sum (u := Finset.univ) fun j _ => (hd a j).mul_const (v j)
  · exact tendsto_finsetSum Finset.univ fun j _ => (hY a j).mul_const (v j)

def extend {N p : ℕ} (Y : Matrix (Fin N) (Fin p) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun a b => if h : (b : ℕ) < p then Y a ⟨b, h⟩ else (1 : Matrix (Fin N) (Fin N) ℂ) a b

theorem extend_submatrix {N p : ℕ} (hp : p ≤ N) (Y : Matrix (Fin N) (Fin p) ℂ) :
    (extend Y).submatrix id (Fin.castLE hp) = Y := by
  ext a j
  simp [extend]

theorem det_extend {N p : ℕ} {hp : p ≤ N} {Y : Matrix (Fin N) (Fin p) ℂ} (h : IsGraph hp Y) : (extend Y).det = 1 := by
  have key : ∀ a b : Fin N, a ≤ b → extend Y a b = (1 : Matrix (Fin N) (Fin N) ℂ) a b := fun a b hab => by
    rw [extend, of_apply]
    split_ifs with hb
    · have ha : (a : ℕ) < p := lt_of_le_of_lt hab hb
      have := congrFun (congrFun h.1 ⟨a, ha⟩) ⟨b, hb⟩
      by_cases hab : a = b
      · subst b
        simpa [one_apply] using this
      · have hab' : (⟨a, ha⟩ : Fin p) ≠ ⟨b, hb⟩ := by
          intro heq
          apply hab
          exact Fin.ext (congrArg (fun x : Fin p => x.val) heq)
        simpa [one_apply, hab, hab'] using this
    · rfl
  rw [det_of_isLowerTriangular _ fun a b hab => by
    have hab' : a < b := hab
    rw [key a b hab'.le, one_apply_ne hab'.ne]]
  simp [key]

theorem span_col {N p : ℕ} (hp : p ≤ N) (m : Matrix (Fin N) (Fin N) ℂ) :
    Submodule.span ℂ (ReciprocityTheory.ChartRestriction.G.FD.col m '' {a | (a : ℕ) < p}) =
      LinearMap.range (m.submatrix id (Fin.castLE hp)).mulVecLin := by
  rw [range_mulVecLin]
  congr 1
  ext v
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, ha⟩, rfl⟩
  · rintro ⟨j, rfl⟩
    exact ⟨Fin.castLE hp j, j.2, rfl⟩

theorem submatrix_mul_upper {N p : ℕ} (hp : p ≤ N) (y b : Matrix (Fin N) (Fin N) ℂ)
    (hb : ∀ a c, c < a → b a c = 0) :
    (y * b).submatrix id (Fin.castLE hp) =
      y.submatrix id (Fin.castLE hp) * b.submatrix (Fin.castLE hp) (Fin.castLE hp) := by
  ext a j
  simp only [submatrix_apply, Matrix.mul_apply, id]
  rw [sum_castLE hp fun k => y a k * b k (Fin.castLE hp j)]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs with hk
  · rfl
  · rw [hb k _ (by have := j.2; simp only [Fin.lt_def, Fin.val_castLE]; omega), mul_zero]

theorem gramPos_iff {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {N : ℕ} (X : Data E N)
    {x : Frame X.Ψ N} {τ : X.Ψ} {P y : Matrix (Fin N) (Fin N) ℂ} (hP : gram τ.1 X.Gm P = Jm N X.p0)
    (hx : mat x τ = P * y) :
    (X.gramPos x τ).PosDef ↔ ((y.submatrix id (Fin.castLE X.p0_le))ᴴ * Jm N X.p0 *
      y.submatrix id (Fin.castLE X.p0_le)).PosDef := by
  have h1 : (X.gramPos x τ)ᵀ = (y.submatrix id (Fin.castLE X.p0_le))ᴴ * Jm N X.p0 *
      y.submatrix id (Fin.castLE X.p0_le) := by
    have h2 : (gram τ.1 X.Gm (mat x τ))ᵀ = yᴴ * Jm N X.p0 * y := by
      rw [hx, FrameDegreeData.gram_mul, hP, transpose_mul, transpose_mul, transpose_transpose, Jm, diagonal_transpose,
        Matrix.mul_assoc]
      rfl
    rw [Data.gramPos, transpose_submatrix, h2]
    rfl
  rw [← h1]
  exact ⟨fun h => h.transpose, fun h => by simpa using h.transpose⟩

theorem orbit_limit : ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (N : ℕ) (X : Data E N) (T : ℝ)
    (M : ℕ) (x : ℂ → Frame X.Ψ N), IsOrbit X T M 1 x → ∃ x₀ ∈ X.dom, ∃ x' : ℂ → Frame X.Ψ N,
      Tendsto x' imTop (𝓝 x₀) ∧ ∀ᶠ w in imTop, x' w ∈ X.dom ∧ SamePos X (x w) (x' w) := by
  intro E _ _ _ N X T M x ⟨hM, _, hd, hdom, hper⟩
  choose P hP0 hP using X.signature
  have hp := X.p0_le
  let U : X.Ψ → ℂ → Matrix (Fin N) (Fin X.p0) ℂ := fun τ w => ((P τ)⁻¹ * mat (x w) τ).submatrix id (Fin.castLE hp)
  let Y : X.Ψ → ℂ → Matrix (Fin N) (Fin X.p0) ℂ := fun τ w => U τ w * ((U τ w).submatrix (Fin.castLE hp) id)⁻¹
  have hx : ∀ τ w, mat (x w) τ = P τ * ((P τ)⁻¹ * mat (x w) τ) := fun τ w =>
    (mul_nonsing_inv_cancel_left _ _ (hP0 τ).isUnit).symm
  have hU : ∀ τ (w : ℂ), T < w.im → ((U τ w)ᴴ * Jm N X.p0 * U τ w).PosDef := fun τ w hw =>
    (gramPos_iff X (hP τ) (hx τ w)).1 (X.gramPos_posDef (hdom w hw) τ)
  have hUd : ∀ τ a j, DifferentiableOn ℂ (fun w => U τ w a j) {w | T < w.im} := fun τ a j =>
    DifferentiableOn.fun_sum (u := Finset.univ) fun k _ =>
      (differentiableOn_pi.1 (differentiableOn_pi.1 (differentiableOn_pi.1 hd τ) k) (Fin.castLE hp j)).const_mul
        ((P τ)⁻¹ a k)
  have hG : ∀ τ (w : ℂ), T < w.im → IsGraph hp (Y τ w) := fun τ w hw => isGraph_mul_inv hp (hU τ w hw)
  have hlim : ∀ τ, ∃ Y₀, IsGraph hp Y₀ ∧ ∀ a j, Tendsto (fun w => Y τ w a j) imTop (𝓝 (Y₀ a j)) := fun τ => by
    refine graph_limit hp (T := T) (h := M) (by exact_mod_cast hM) (fun a j => ?_) (fun w hw => ?_) (hG τ)
    · exact DifferentiableOn.fun_sum (u := Finset.univ) fun k _ => (hUd τ a k).fun_mul
        (GlobalTheory.TorsionHolomorphic.differentiableOn_matrix_inv (fun w => (U τ w).submatrix (Fin.castLE hp) id) _
          (fun i l => hUd τ _ l) (fun w hw => det_top_ne hp (hU τ w hw)) k j)
    · obtain ⟨b, hb, -, hxb⟩ := hper w hw
      have h1 : mat (x (w + M)) τ = mat (x w) τ * mat b τ := by
        rw [hxb]
        show ((1 : GL (Fin N) E) : Matrix (Fin N) (Fin N) E).map τ.1 * mat (x w) τ * mat b τ = _
        simp
      set c := (mat b τ).submatrix (Fin.castLE hp) (Fin.castLE hp) with hc
      have h2 : U τ (w + M) = U τ w * c := by
        simp only [U]
        rw [h1, ← Matrix.mul_assoc, submatrix_mul_upper hp _ (mat b τ) (hb τ).2]
      have h3 : (U τ w * c).submatrix (Fin.castLE hp) id = (U τ w).submatrix (Fin.castLE hp) id * c := rfl
      have h4 := det_top_ne hp (hU τ (w + M) (by simpa using hw))
      rw [h2, h3, det_mul] at h4
      simp only [Y, Complex.ofReal_natCast]
      rw [h2, h3, Matrix.mul_inv_rev, Matrix.mul_assoc,
        mul_nonsing_inv_cancel_left _ _ (right_ne_zero_of_mul h4).isUnit]
  choose Y₀ hY₀ hlim using hlim
  let fr : (X.Ψ → Matrix (Fin N) (Fin X.p0) ℂ) → Frame X.Ψ N := fun Z τ =>
    (P τ * extend (Z τ) : Matrix (Fin N) (Fin N) ℂ)
  have hfr : ∀ Z τ, mat (fr Z) τ = P τ * extend (Z τ) := fun _ _ => rfl
  have hmem : ∀ Z, (∀ τ, IsGraph hp (Z τ)) → fr Z ∈ X.dom := fun Z hZ =>
    ReciprocityTheory.ChartRestriction.G.AR.Up.ExF.mem_dom_of_gramPos X fun τ => ⟨by
      rw [hfr, det_mul, det_extend (hZ τ), mul_one]
      exact hP0 τ, (gramPos_iff X (hP τ) (hfr Z τ)).2 (by rw [extend_submatrix]; exact (hZ τ).2)⟩
  refine ⟨fr Y₀, hmem _ hY₀, fun w => fr fun τ => Y τ w, ?_, (eventually_imTop T).mono fun w hw =>
    ⟨hmem _ fun τ => hG τ w hw, fun τ => ?_⟩⟩
  · refine tendsto_pi_nhds.2 fun τ => tendsto_pi_nhds.2 fun a => tendsto_pi_nhds.2 fun b => ?_
    refine tendsto_finsetSum Finset.univ (f := fun k w => P τ a k * extend (Y τ w) k b)
      (a := fun k => P τ a k * extend (Y₀ τ) k b) fun k _ => Tendsto.const_mul _ ?_
    simp only [extend, of_apply]
    split_ifs with hb
    · exact hlim τ k _
    · exact tendsto_const_nhds
  · have h1 : (mat (x w) τ).submatrix id (Fin.castLE hp) = P τ * U τ w := by
      conv_lhs => rw [hx τ w]
      rfl
    have h2 : (P τ * extend (Y τ w)).submatrix id (Fin.castLE hp) =
        P τ * U τ w * ((U τ w).submatrix (Fin.castLE hp) id)⁻¹ := by
      rw [Matrix.mul_assoc, ← extend_submatrix hp (U τ w * _)]
      rfl
    rw [span_col hp, span_col hp, hfr, h1, h2, mulVecLin_mul (P τ * U τ w), LinearMap.range_comp_of_range_eq_top]
    exact LinearMap.range_eq_top.2 (mulVec_surjective_iff_isUnit.2
      ((isUnit_iff_isUnit_det _).2 (isUnit_nonsing_inv_det _ (det_top_ne hp (hU τ w hw)).isUnit)))

end GlobalTheory.ShFam.OrbitLimit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrivialMonodromyOrbitConvergesSymmetricDomainStatement
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trivial_monodromy_orbit_converges_symmetric_domain : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (X : Data E N) (T : ℝ) (M : ℕ) (x : ℂ → Frame X.Ψ N), IsOrbit X T M 1 x → ∃ x₀ ∈ X.dom, ∃ x' : ℂ → Frame X.Ψ N, Tendsto x' imTop (𝓝 x₀) ∧ ∀ᶠ w in imTop, x' w ∈ X.dom ∧ SamePos X (x w) (x' w) := by
  first | exact @GlobalTheory.ShFam.OrbitLimit.orbit_limit | exact GlobalTheory.ShFam.OrbitLimit.orbit_limit | (intros; apply GlobalTheory.ShFam.OrbitLimit.orbit_limit <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeromorphicGermVanishesOfPeriodicExpModulus
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeromorphicGermVanishesOfPeriodicExpModulus
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)

namespace GlobalTheory.ShFam.BdArc

theorem not_eventually_re_pos_of_periodic {f : ℂ → ℂ} {M : ℝ} (hM : 0 < M) (hper : Function.Periodic f M)
    (hd : ∀ᶠ z in imTop, DifferentiableAt ℂ f z) (h0 : Tendsto f imTop (𝓝 0)) :
    ¬ ∀ᶠ z in imTop, 0 < (f z).re := by
  intro hpos
  set F := Function.Periodic.cuspFunction M f with hF
  have hF0 : F 0 = 0 := Function.Periodic.cuspFunction_zero_of_zero_at_inf hM h0
  have hd0 : DifferentiableAt ℂ F 0 :=
    Function.Periodic.differentiableAt_cuspFunction_zero hM hper hd
      (Filter.ZeroAtFilter.boundedAtFilter (l := comap Complex.im atTop) (f := f) h0)
  have hd1 : ∀ᶠ q in 𝓝[≠] 0, DifferentiableAt ℂ F q :=
    Function.Periodic.eventually_differentiableAt_cuspFunction_nhds_ne_zero hM hper hd
  have hp1 : ∀ᶠ q in 𝓝[≠] (0 : ℂ), 0 < (F q).re := by
    filter_upwards [(Function.Periodic.invQParam_tendsto hM).eventually hpos, self_mem_nhdsWithin] with q hq hq0
    rwa [hF, Function.Periodic.cuspFunction_eq_of_nonzero _ _ hq0]
  have hd2 : ∀ᶠ q in 𝓝 (0 : ℂ), DifferentiableAt ℂ (fun z => Complex.exp (-F z)) q := by
    filter_upwards [eventually_nhdsWithin_iff.mp hd1] with q hq
    by_cases hq0 : q = 0
    · subst hq0; exact hd0.neg.cexp
    · exact (hq hq0).neg.cexp
  have hmax : IsLocalMax (norm ∘ fun z => Complex.exp (-F z)) 0 := by
    filter_upwards [eventually_nhdsWithin_iff.mp hp1] with q hq
    by_cases hq0 : q = 0
    · subst hq0; exact le_rfl
    · have := hq hq0
      simp only [Function.comp, Complex.norm_exp, hF0, Complex.neg_re, Real.exp_le_exp]
      simpa using this.le
  have hc := Complex.eventually_eq_of_isLocalMax_norm hd2 hmax
  obtain ⟨q, hq1, hq2⟩ := (hp1.and (hc.filter_mono nhdsWithin_le_nhds)).exists
  have := congrArg norm hq2
  simp only [Complex.norm_exp, hF0, Complex.neg_re, Real.exp_eq_exp] at this
  simp at this
  exact hq1.ne' this

theorem not_tendsto_re_atTop_of_periodic {L : ℂ → ℂ} {T M : ℝ} (hM : 0 < M)
    (hd : DifferentiableOn ℂ L {w | T < w.im}) (hper : ∀ w : ℂ, T < w.im → L (w + M) = L w) :
    ¬ Tendsto (fun w => (L w).re) imTop atTop := by
  intro ht
  have hT : ∀ᶠ w in imTop, T < w.im := (tendsto_comap (f := Complex.im) (x := atTop)).eventually (eventually_gt_atTop T)
  have hopen : IsOpen {w : ℂ | T < w.im} := isOpen_lt continuous_const Complex.continuous_im
  have hpos : ∀ᶠ w in imTop, 0 < (L w).re := ht.eventually (eventually_gt_atTop 0)
  classical
  set f : ℂ → ℂ := fun w => if T < w.im then (L w)⁻¹ else 0 with hf
  have hfe : ∀ w : ℂ, T < w.im → f w = (L w)⁻¹ := fun w hw => if_pos hw
  refine not_eventually_re_pos_of_periodic (f := f) hM ?_ ?_ ?_ ?_
  · intro w
    by_cases hw : T < w.im
    · have hw' : T < (w + M).im := by simpa using hw
      rw [hfe _ hw, hfe _ hw', hper w hw]
    · have hw' : ¬ T < (w + M).im := by simpa using hw
      simp only [hf, if_neg hw, if_neg hw']
  · filter_upwards [hT, hpos] with w hw hw0
    have hne : L w ≠ 0 := fun h => by simp [h] at hw0
    refine ((hd.differentiableAt (hopen.mem_nhds hw)).inv hne).congr_of_eventuallyEq ?_
    filter_upwards [hopen.mem_nhds hw] with z hz using hfe z hz
  · have h1 : Tendsto (fun w => ‖L w‖) imTop atTop :=
      tendsto_atTop_mono (fun w => Complex.re_le_norm (L w)) ht
    have h2 : Tendsto (fun w => (L w)⁻¹) imTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      simp only [norm_inv]
      exact h1.inv_tendsto_atTop
    refine h2.congr' ?_
    filter_upwards [hT] with w hw using (hfe w hw).symm
  · filter_upwards [hT, hpos] with w hw hw0
    have hne : L w ≠ 0 := fun h => by simp [h] at hw0
    rw [hfe w hw, Complex.inv_re]
    exact div_pos hw0 (Complex.normSq_pos.mpr hne)

theorem tendsto_zero_of_norm_eq_mul_exp_periodic :
    ∀ (p L h a b : ℂ → ℂ) (T r : ℝ) (M n : ℕ) (ζ : ℂ), 0 < M → 0 < n → ζ ^ n = 1 → 0 < r → DifferentiableOn ℂ p {w | T < w.im} → DifferentiableOn ℂ L {w | T < w.im} → (∀ w : ℂ, T < w.im → p (w + M) = ζ * p w ∧ L (w + M) = L w ∧ ‖h (eTwoPi w)‖ = ‖p w‖ * ‖Complex.exp (L w)‖) → Tendsto p imTop (𝓝 0) → DifferentiableOn ℂ a (Metric.ball (0 : ℂ) r) → DifferentiableOn ℂ b (Metric.ball (0 : ℂ) r) → (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → b u ≠ 0 ∧ h u * b u = a u) → Tendsto h (𝓝[≠] 0) (𝓝 0) := by
  intro p L h a b T r M n ζ hM _ _ hr _ hL hw hp ha hb hab
  have hball : Metric.ball (0 : ℂ) r ∈ 𝓝 (0 : ℂ) := Metric.ball_mem_nhds _ hr
  have hmer : MeromorphicAt h 0 := by
    refine ((ha.analyticAt hball).meromorphicAt.div (hb.analyticAt hball).meromorphicAt).congr ?_
    filter_upwards [mem_nhdsWithin_of_mem_nhds hball, self_mem_nhdsWithin] with u hu hu0
    obtain ⟨h1, h2⟩ := hab u hu hu0
    simp only [Pi.div_apply]
    rw [← h2, mul_div_cancel_right₀ _ h1]
  rw [tendsto_zero_iff_meromorphicOrderAt_pos hmer]
  by_contra hord
  rw [not_lt] at hord
  have hne : ∀ᶠ u in 𝓝[≠] (0 : ℂ), h u ≠ 0 :=
    (meromorphicOrderAt_ne_top_iff_eventually_ne_zero hmer).mp (fun ht => by simp [ht] at hord)
  obtain ⟨c, hc⟩ : ∃ c, Tendsto h⁻¹ (𝓝[≠] 0) (𝓝 c) := by
    rw [tendsto_nhds_iff_meromorphicOrderAt_nonneg hmer.inv, meromorphicOrderAt_inv]
    induction hk : meromorphicOrderAt h 0 with
    | top => simp
    | coe k =>
      rw [hk] at hord
      have hk0 : k ≤ 0 := by exact_mod_cast hord
      have : (0 : ℤ) ≤ -k := by omega
      exact_mod_cast this
  have he : Tendsto eTwoPi imTop (𝓝[≠] 0) := by
    refine (Function.Periodic.qParam_tendsto (h := 1) one_pos).congr fun w => ?_
    simp [Function.Periodic.qParam, eTwoPi]
  have hT : ∀ᶠ w in imTop, T < w.im := (tendsto_comap (f := Complex.im) (x := atTop)).eventually (eventually_gt_atTop T)
  refine not_tendsto_re_atTop_of_periodic (M := (M : ℝ)) (by exact_mod_cast hM) hL
    (fun w hw' => by simpa using (hw w hw').2.1) ?_
  rw [← tendsto_neg_atBot_iff, ← Real.tendsto_exp_comp_nhds_zero]
  have h1 := hp.norm.mul (hc.comp he).norm
  simp only [norm_zero, zero_mul] at h1
  refine h1.congr' ?_
  filter_upwards [hT, he.eventually hne] with w hw' hw0
  have h2 := (hw w hw').2.2
  have h3 : ‖h (eTwoPi w)‖ ≠ 0 := norm_ne_zero_iff.mpr hw0
  simp only [Function.comp, Pi.inv_apply, norm_inv]
  rw [Complex.norm_exp] at h2
  rw [Real.exp_neg, ← div_eq_mul_inv, div_eq_iff h3, h2]
  field_simp

end GlobalTheory.ShFam.BdArc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeromorphicGermVanishesOfPeriodicExpModulusStatement
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.meromorphic_germ_vanishes_of_periodic_exp_modulus : ∀ (p L h a b : ℂ → ℂ) (T r : ℝ) (M n : ℕ) (ζ : ℂ), 0 < M → 0 < n → ζ ^ n = 1 → 0 < r → DifferentiableOn ℂ p {w | T < w.im} → DifferentiableOn ℂ L {w | T < w.im} → (∀ w : ℂ, T < w.im → p (w + M) = ζ * p w ∧ L (w + M) = L w ∧ ‖h (eTwoPi w)‖ = ‖p w‖ * ‖Complex.exp (L w)‖) → Tendsto p imTop (𝓝 0) → DifferentiableOn ℂ a (Metric.ball (0 : ℂ) r) → DifferentiableOn ℂ b (Metric.ball (0 : ℂ) r) → (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → b u ≠ 0 ∧ h u * b u = a u) → Tendsto h (𝓝[≠] 0) (𝓝 0) := by
  first | exact @GlobalTheory.ShFam.BdArc.tendsto_zero_of_norm_eq_mul_exp_periodic | exact GlobalTheory.ShFam.BdArc.tendsto_zero_of_norm_eq_mul_exp_periodic | (intros; apply GlobalTheory.ShFam.BdArc.tendsto_zero_of_norm_eq_mul_exp_periodic <;> assumption)
end
end

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)

namespace GlobalTheory.ShFam.BdArc

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem tendsto_pow_mul_exp (C C' c c' T : ℝ) (B : ℕ) (hc : 0 < c) (hc' : 0 < c') :
    Tendsto (fun w : ℂ => C * Real.exp (-c * (c' * (w.im - T))) * (C' * w.im ^ B)) imTop (𝓝 0) := by
  have h1 : Tendsto (fun t : ℝ => t ^ B * Real.exp (-(c * c') * t)) atTop (𝓝 0) := by
    have := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (B : ℝ) (c * c') (mul_pos hc hc')
    simpa only [Real.rpow_natCast] using this
  have h2 := (h1.const_mul (C * C' * Real.exp (c * c' * T))).comp (tendsto_comap (f := Complex.im))
  rw [mul_zero] at h2
  refine h2.congr fun w => ?_
  have : Real.exp (-c * (c' * (w.im - T))) = Real.exp (c * c' * T) * Real.exp (-(c * c') * w.im) := by
    rw [← Real.exp_add]; congr 1; ring
  simp only [Function.comp, this]
  ring

theorem tendsto_cusp {N : ℕ} {X : Data E N} {T : ℝ} {x : ℂ → Frame X.Ψ N} {la : Wt X.Ψ N} {P : Frame X.Ψ N → ℂ}
    (hP : P ∈ X.SS la) (hd : ∀ w : ℂ, T < w.im → x w ∈ X.dom) {ξ : Fin N → E} {c' : ℝ} (hξ : X.IsIso ξ) (hc' : 0 < c')
    (ht : ∀ w : ℂ, T + 1 < w.im → ∀ τ, c' * (w.im - T) ≤ X.tt ξ (x w) τ) {C' : ℝ} {B : ℕ}
    (hn : ∀ᶠ w in imTop, 0 < X.nfac la (x w) ∧ (X.nfac la (x w))⁻¹ ≤ C' * w.im ^ B) :
    Tendsto (fun w => P (x w)) imTop (𝓝 0) := by
  obtain ⟨C, c, hc, hC⟩ := GlobalTheory.T.pnorm_le_exp_neg_of_mem_SS_of_isIso E N X la P ξ hP hξ
  refine squeeze_zero_norm' ?_ (tendsto_pow_mul_exp C C' c c' T B hc hc')
  have he : ∀ᶠ w in imTop, T + 1 + 1 / c' < w.im :=
    (tendsto_comap (f := Complex.im)).eventually (eventually_gt_atTop _)
  filter_upwards [hn, he] with w h1 h2
  have h0 : 0 < 1 / c' := by positivity
  have h3 : 1 ≤ c' * (w.im - T) := by
    have : 1 / c' ≤ w.im - T := by linarith
    rwa [div_le_iff₀' hc'] at this
  have h4 := hC (x w) (hd w (by linarith)) _ h3 (ht w (by linarith))
  have h5 : ‖P (x w)‖ = X.pnorm la P (x w) * (X.nfac la (x w))⁻¹ := by
    show _ = ‖P (x w)‖ * X.nfac la (x w) * _
    rw [mul_assoc, mul_inv_cancel₀ h1.1.ne', mul_one]
  have h6 : 0 ≤ X.pnorm la P (x w) := mul_nonneg (norm_nonneg _) h1.1.le
  rw [h5]
  exact mul_le_mul h4 h1.2 (inv_nonneg.2 h1.1.le) (h6.trans h4)

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type}
  [CommRing O] {β : O →+* c.F}

end GlobalTheory.ShFam.BdArc
