module

public import Formalism.UnipotentAdelicQuotients.EllipticRegularity.WeightedNormFinite
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsSideFurther
public import Formalism.UnipotentAdelicQuotients.EllipticRegularity.PairingFourier
public import Formalism.UnipotentAdelicQuotients.EllipticRegularity.Decompose
public import Formalism.UnipotentAdelicQuotients.EllipticRegularity.ExistsSmoothExt
public import Formalism.UnipotentAdelicQuotients.EllipticRegularity.StepCore

@[expose] public section

section -- merged from Formalism.UnipotentAdelicQuotients.EllipticRegularity.SmoothOfLocallySmooth
namespace ZetaZeros.D.EllReg

open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal

theorem integralFourierChar : FourierPair := by
  intro d g _ _ ξ
  rw [Real.fourier_eq']
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  show g y * eF ξ y = Complex.exp (((-2 * Real.pi * inner ℝ y ξ : ℝ) : ℂ) * Complex.I) • g y
  rw [smul_eq_mul, mul_comm (Complex.exp _)]
  congr 1
  simp only [eF]
  congr 1
  push_cast
  ring

theorem existsBump : Bump := by
  intro d x0 r hr
  let f : ContDiffBump x0 := ⟨r / 4, r / 2, by positivity, by linarith⟩
  refine ⟨f, f.contDiff, f.hasCompactSupport, ?_, ?_⟩
  · rw [f.tsupport_eq]
    exact closedBall_subset_ball (show r / 2 < r by linarith)
  · filter_upwards [ball_mem_nhds x0 (show (0 : ℝ) < r / 4 by positivity)] with y hy
    exact f.one_of_mem_closedBall (ball_subset_closedBall hy)

theorem cutoffContinuous : CutCont := by
  intro d U u χ hU hu hχs hχc hχt
  have hχ' : Continuous (fun x => (χ x : ℂ)) := Complex.continuous_ofReal.comp hχs.continuous
  have hsub : tsupport (cut χ u) ⊆ tsupport χ := by
    apply closure_mono
    intro x hx
    by_contra h0
    apply hx
    have h0' : χ x = 0 := by simpa using h0
    simp [cut, h0']
  have hcont : ContinuousOn (cut χ u) U := hχ'.continuousOn.mul hu
  exact ⟨hcont.continuous_of_tsupport_subset hU (hsub.trans hχt),
    IsCompact.of_isClosed_subset hχc (isClosed_tsupport _) hsub⟩

theorem smoothOfLocallySmooth : LocalGlobal := by
  intro d U f _ h x hx
  obtain ⟨χ, hχ1, hχf⟩ := h x hx
  have heq : cut χ f =ᶠ[𝓝 x] f := by
    filter_upwards [hχ1] with y hy
    simp [cut, hy]
  exact (hχf.contDiffAt.congr_of_eventuallyEq heq.symm).contDiffWithinAt

end ZetaZeros.D.EllReg
end

section -- merged from Formalism.UnipotentAdelicQuotients.EllipticRegularity.PairingLocal
namespace ZetaZeros.D.EllReg

open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal

lemma dw_eventuallyEq {d : ℕ} (w : List (Fin d)) {f f' : E d → ℂ} {y : E d} (h : f =ᶠ[𝓝 y] f') :
    dw w f =ᶠ[𝓝 y] dw w f' := by
  induction w with
  | nil => simpa [dw] using h
  | cons j w ih =>
    filter_upwards [ih.fderiv (𝕜 := ℝ)] with x hx
    show fderiv ℝ (dw w f) x (ev j) = fderiv ℝ (dw w f') x (ev j)
    rw [hx]

theorem adjointPairingLocal : PairingLocal := by
  intro d m b b' g φ V hV hg hb
  congr 1
  funext y
  by_cases hy : y ∈ V
  · congr 1
    unfold trOp
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun w _ => ?_
    congr 1

    have hev : (fun y => b n w y * φ y) =ᶠ[𝓝 y] (fun y => b' n w y * φ y) := by
      filter_upwards [hV.mem_nhds hy] with z hz
      rw [hb n w z hz]
    exact (dw_eventuallyEq _ hev).eq_of_nhds
  · have hg0 : g y = 0 := by
      first
        | exact image_eq_zero_of_nmem_tsupport (fun h => hy (hg h))
        | exact image_eq_zero_of_notMem_tsupport (fun h => hy (hg h))
    rw [hg0, zero_mul, zero_mul]

end ZetaZeros.D.EllReg
end

section -- merged from Formalism.UnipotentAdelicQuotients.EllipticRegularity.IteratedPartialFourierChar
namespace ZetaZeros.D.EllReg

open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal

noncomputable def eL {d : ℕ} (ξ : E d) : E d →L[ℝ] ℂ :=
  (-(2 * (Real.pi : ℂ) * Complex.I)) • (Complex.ofRealCLM.comp (innerSL ℝ ξ))

lemma eF_eq_exp {d : ℕ} (ξ : E d) : eF ξ = fun y => Complex.exp (eL ξ y) := by
  funext y
  simp only [eF, eL, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply, Complex.ofRealCLM_apply, smul_eq_mul, real_inner_comm y ξ]
  ring_nf

lemma hasFDerivAt_eF {d : ℕ} (ξ y : E d) :
    HasFDerivAt (eF ξ) (Complex.exp (eL ξ y) • eL ξ) y := by
  rw [eF_eq_exp]
  exact (eL ξ).hasFDerivAt.cexp

lemma eL_ev {d : ℕ} (ξ : E d) (j : Fin d) : eL ξ (ev j) = -(2 * Real.pi * Complex.I * ((ξ j : ℝ) : ℂ)) := by
  simp only [eL, ev, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply, Complex.ofRealCLM_apply, smul_eq_mul, EuclideanSpace.inner_single_right]
  simp

theorem iteratedPartialFourierChar : DwExp := by
  intro d ξ w
  induction w with
  | nil => funext y; simp [dw]
  | cons j w ih =>
    funext x
    have hfun : dw w (eF ξ) =
        fun y => (w.map fun j => -(2 * Real.pi * Complex.I * ((ξ j : ℝ) : ℂ))).prod * eF ξ y := ih
    show fderiv ℝ (dw w (eF ξ)) x (ev j) = _
    rw [hfun, ((hasFDerivAt_eF ξ x).const_mul _).fderiv]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, eL_ev, List.map_cons, List.prod_cons,
      eF_eq_exp]
    ring

end ZetaZeros.D.EllReg
end

section -- merged from Formalism.UnipotentAdelicQuotients.EllipticRegularity.WeakFourier
namespace ZetaZeros.D.EllReg

open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal

noncomputable section

namespace WF

variable {d : ℕ}

def ev (L : List (List (Fin d) × (E d → ℂ))) (g : E d → ℂ) (y : E d) : ℂ :=
  (L.map fun p => p.2 y * dw p.1 g y).sum

def Good (k : ℕ) (K : Set (E d)) (L : List (List (Fin d) × (E d → ℂ))) : Prop :=
  ∀ p ∈ L, p.1.length < k ∧ ContDiff ℝ ∞ p.2 ∧ ∀ y ∉ K, p.2 y = 0

def Dk (k : Fin d) (f : E d → ℂ) : E d → ℂ := fun y => fderiv ℝ f y (ZetaZeros.D.EllReg.ev k)

theorem dw_cons (k : Fin d) (w : List (Fin d)) (f : E d → ℂ) : dw (k :: w) f = Dk k (dw w f) := rfl

private theorem contDiff_fderiv'_lemma_2 {f : ZetaZeros.D.EllReg.E d → ℂ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (fderiv ℝ f) := by
  exact (contDiff_infty_iff_fderiv.mp hf).2

theorem contDiff_Dk {f : E d → ℂ} (hf : ContDiff ℝ ∞ f) (k : Fin d) : ContDiff ℝ ∞ (Dk k f) := by
  exact (contDiff_fderiv'_lemma_2 hf).clm_apply contDiff_const

theorem contDiff_dw {f : E d → ℂ} (hf : ContDiff ℝ ∞ f) : ∀ w : List (Fin d), ContDiff ℝ ∞ (dw w f)
  | [] => hf
  | k :: w => contDiff_Dk (contDiff_dw hf w) k

theorem Dk_zero_off {f : E d → ℂ} {K : Set (E d)} (hK : IsClosed K) (hf : ∀ y ∉ K, f y = 0) (k : Fin d) :
    ∀ y ∉ K, Dk k f y = 0 := by
  intro y hy
  have h : f =ᶠ[𝓝 y] fun _ => (0 : ℂ) := by
    filter_upwards [hK.isOpen_compl.mem_nhds hy] with z hz
    exact hf z hz
  show fderiv ℝ f y (ZetaZeros.D.EllReg.ev k) = 0
  rw [h.fderiv_eq]
  simp

private theorem differentiable_of_contDiff'_lemma {f : ZetaZeros.D.EllReg.E d → ℂ} (hf : ContDiff ℝ ∞ f) : Differentiable ℝ f := by
  exact (contDiff_infty_iff_fderiv.mp hf).1

theorem Dk_add {f g : E d → ℂ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (k : Fin d) (y : E d) :
    Dk k (fun z => f z + g z) y = Dk k f y + Dk k g y := by
  have H := ((differentiable_of_contDiff'_lemma hf y).hasFDerivAt.add (differentiable_of_contDiff'_lemma hg y).hasFDerivAt).fderiv
  show fderiv ℝ (f + g) y (ZetaZeros.D.EllReg.ev k) = fderiv ℝ f y (ZetaZeros.D.EllReg.ev k) + fderiv ℝ g y (ZetaZeros.D.EllReg.ev k)
  rw [H]
  rfl

theorem Dk_mul {f g : E d → ℂ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (k : Fin d) (y : E d) :
    Dk k (fun z => f z * g z) y = Dk k f y * g y + f y * Dk k g y := by
  have H := ((differentiable_of_contDiff'_lemma hf y).hasFDerivAt.mul (differentiable_of_contDiff'_lemma hg y).hasFDerivAt).fderiv
  show fderiv ℝ (f * g) y (ZetaZeros.D.EllReg.ev k) = fderiv ℝ f y (ZetaZeros.D.EllReg.ev k) * g y + f y * fderiv ℝ g y (ZetaZeros.D.EllReg.ev k)
  rw [H]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem contDiff_ev {L : List (List (Fin d) × (E d → ℂ))} (hL : ∀ p ∈ L, ContDiff ℝ ∞ p.2)
    {g : E d → ℂ} (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (ev L g) := by
  revert hL
  induction L with
  | nil =>
    intro _
    have h0 : ev ([] : List (List (Fin d) × (ZetaZeros.D.EllReg.E d → ℂ))) g = fun _ => 0 := by
      funext y; simp only [ev, List.map_nil, List.sum_nil]
    rw [h0]; exact contDiff_const
  | cons p L ih =>
    intro hL
    have h1 : ev (p :: L) g = fun y => p.2 y * ZetaZeros.D.EllReg.dw p.1 g y + ev L g y := by
      funext y; simp only [ev, List.map_cons, List.sum_cons]
    rw [h1]
    exact ((hL p (by simp)).mul (contDiff_dw hg p.1)).add (ih fun q hq => hL q (by simp [hq]))

theorem ev_cons (p : List (Fin d) × (E d → ℂ)) (L : List (List (Fin d) × (E d → ℂ))) (g : E d → ℂ) (y : E d) :
    ev (p :: L) g y = p.2 y * dw p.1 g y + ev L g y := by
  simp only [ev, List.map_cons, List.sum_cons]

theorem ev_nil (g : E d → ℂ) (y : E d) : ev ([] : List (List (Fin d) × (E d → ℂ))) g y = 0 := by
  simp only [ev, List.map_nil, List.sum_nil]

theorem ev_append (L1 L2 : List (List (Fin d) × (E d → ℂ))) (g : E d → ℂ) (y : E d) :
    ev (L1 ++ L2) g y = ev L1 g y + ev L2 g y := by
  simp only [ev, List.map_append, List.sum_append]

def sc (C : E d → ℂ) (L : List (List (Fin d) × (E d → ℂ))) : List (List (Fin d) × (E d → ℂ)) :=
  L.map fun p => (p.1, fun y => C y * p.2 y)

theorem ev_sc (C : E d → ℂ) (L : List (List (Fin d) × (E d → ℂ))) (g : E d → ℂ) (y : E d) :
    ev (sc C L) g y = C y * ev L g y := by
  induction L with
  | nil => simp only [sc, List.map_nil, ev_nil, mul_zero]
  | cons p L ih =>
    have h1 : sc C (p :: L) = (p.1, fun z => C z * p.2 z) :: sc C L := rfl
    rw [h1]
    simp only [ev_cons, ih]
    ring

theorem Dk_ev {L : List (List (Fin d) × (E d → ℂ))} (hL : ∀ p ∈ L, ContDiff ℝ ∞ p.2)
    {g : E d → ℂ} (hg : ContDiff ℝ ∞ g) (k : Fin d) (y : E d) :
    Dk k (ev L g) y = ev (L.map fun p => (p.1, Dk k p.2)) g y + ev (L.map fun p => (k :: p.1, p.2)) g y := by
  revert hL
  induction L with
  | nil =>
    intro _
    have h0 : ev ([] : List (List (Fin d) × (ZetaZeros.D.EllReg.E d → ℂ))) g = fun _ => 0 := by
      funext z; simp only [ev, List.map_nil, List.sum_nil]
    rw [h0]
    simp [Dk, ev]
  | cons p L ih =>
    intro hL
    have hp : ContDiff ℝ ∞ p.2 := hL p (by simp)
    have hL' : ∀ q ∈ L, ContDiff ℝ ∞ q.2 := fun q hq => hL q (by simp [hq])
    have h1 : ev (p :: L) g = fun z => p.2 z * ZetaZeros.D.EllReg.dw p.1 g z + ev L g z := by
      funext z; exact ev_cons p L g z
    rw [h1, Dk_add (hp.mul (contDiff_dw hg p.1)) (contDiff_ev hL' hg) k y,
      Dk_mul hp (contDiff_dw hg p.1) k y, ih hL']
    simp only [List.map_cons, ev_cons, dw_cons]
    ring

def lb : List (Fin d) → (E d → ℂ) → List (List (Fin d) × (E d → ℂ))
  | [], _ => []
  | k :: w, f => (w, Dk k f) :: ((lb w f).map (fun p => (p.1, Dk k p.2)) ++ (lb w f).map (fun p => (k :: p.1, p.2)))

theorem lb_good {f : E d → ℂ} (hf : ContDiff ℝ ∞ f) {K : Set (E d)} (hK : IsClosed K)
    (hfK : ∀ y ∉ K, f y = 0) : ∀ w : List (Fin d), Good w.length K (lb w f)
  | [] => by intro p hp; simp [lb] at hp
  | k :: w => by
    have ih : Good w.length K (lb w f) := lb_good hf hK hfK w
    intro p hp
    simp only [lb, List.mem_cons, List.mem_append, List.mem_map] at hp
    rcases hp with rfl | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · exact ⟨by simp, contDiff_Dk hf k, Dk_zero_off hK hfK k⟩
    · have h := ih q hq
      exact ⟨Nat.lt_succ_of_lt h.1, contDiff_Dk h.2.1 k, Dk_zero_off hK h.2.2 k⟩
    · have h := ih q hq
      exact ⟨Nat.succ_lt_succ h.1, h.2⟩

theorem leib {f : E d → ℂ} (hf : ContDiff ℝ ∞ f) : ∀ (w : List (Fin d)) (g : E d → ℂ), ContDiff ℝ ∞ g →
    dw w (fun z => f z * g z) = fun y => f y * dw w g y + ev (lb w f) g y
  | [], g, hg => by funext y; simp [dw, lb, ev]
  | k :: w, g, hg => by
    have hgood : Good w.length Set.univ (lb w f) := lb_good hf isClosed_univ (by simp) w
    have hc : ∀ p ∈ lb w f, ContDiff ℝ ∞ p.2 := fun p hp => (hgood p hp).2.1
    funext y
    rw [dw_cons, leib hf w g hg, Dk_add (hf.mul (contDiff_dw hg w)) (contDiff_ev hc hg),
      Dk_mul hf (contDiff_dw hg w), Dk_ev hc hg]
    simp only [lb, ev_cons, ev_append, dw_cons]
    ring

def sb (a : E d → ℂ) : List (List (Fin d) × (E d → ℂ)) → List (List (Fin d) × (E d → ℂ))
  | [] => []
  | p :: L => (p.1, fun y => p.2 y * a y) :: (sc p.2 (lb p.1 a) ++ sb a L)

theorem ev_sb {a : E d → ℂ} (ha : ContDiff ℝ ∞ a) {e : E d → ℂ} (he : ContDiff ℝ ∞ e) (y : E d) :
    ∀ L : List (List (Fin d) × (E d → ℂ)), ev L (fun z => a z * e z) y = ev (sb a L) e y
  | [] => by simp [ev, sb]
  | p :: L => by
    rw [ev_cons, ev_sb ha he y L, leib ha p.1 e he]
    simp only [sb, ev_cons, ev_append, ev_sc]
    ring

theorem sb_good {a : E d → ℂ} (ha : ContDiff ℝ ∞ a) {k : ℕ} {K : Set (E d)} :
    ∀ L : List (List (Fin d) × (E d → ℂ)), Good k K L → Good k K (sb a L)
  | [], _ => by intro p hp; simp [sb] at hp
  | p :: L, hL => by
    have hp : p.1.length < k ∧ ContDiff ℝ ∞ p.2 ∧ ∀ y ∉ K, p.2 y = 0 := hL p (by simp)
    have ih : Good k K (sb a L) := sb_good ha L (fun q hq => hL q (by simp [hq]))
    have hlb : Good p.1.length Set.univ (lb p.1 a) := lb_good ha isClosed_univ (by simp) p.1
    intro q hq
    simp only [sb, sc, List.mem_cons, List.mem_append, List.mem_map] at hq
    rcases hq with rfl | ⟨r, hr, rfl⟩ | hq
    · exact ⟨hp.1, hp.2.1.mul ha, fun y hy => by simp [hp.2.2 y hy]⟩
    · have h := hlb r hr
      exact ⟨lt_trans h.1 hp.1, hp.2.1.mul h.2.1, fun y hy => by simp [hp.2.2 y hy]⟩
    · exact ih q hq

theorem good_mono {k k' : ℕ} {K : Set (E d)} {L : List (List (Fin d) × (E d → ℂ))} (hL : Good k K L)
    (hk : k ≤ k') : Good k' K L := by
  intro p hp
  obtain ⟨h1, h2⟩ := hL p hp
  exact ⟨lt_of_lt_of_le h1 hk, h2⟩

def cf (L : List (List (Fin d) × (E d → ℂ))) (n : ℕ) (w : Fin n → Fin d) (y : E d) : ℂ :=
  (L.map fun p => if p.1 = List.ofFn w then p.2 y else 0).sum

theorem cf_good {k : ℕ} {K : Set (E d)} {L : List (List (Fin d) × (E d → ℂ))} (hL : Good k K L)
    (n : ℕ) (w : Fin n → Fin d) : ContDiff ℝ ∞ (cf L n w) ∧ ∀ y ∉ K, cf L n w y = 0 := by
  revert hL
  induction L with
  | nil =>
    intro _
    have h0 : cf ([] : List (List (Fin d) × (ZetaZeros.D.EllReg.E d → ℂ))) n w = fun _ => 0 := by
      funext y; simp only [cf, List.map_nil, List.sum_nil]
    rw [h0]; exact ⟨contDiff_const, fun _ _ => rfl⟩
  | cons p L ih =>
    intro hL
    have hp := hL p (by simp)
    have hL' : Good k K L := by
      intro r hr; exact hL r (by simp [hr])
    obtain ⟨ih1, ih2⟩ := ih hL'
    have h1 : cf (p :: L) n w = fun y => (if p.1 = List.ofFn w then p.2 y else 0) + cf L n w y := by
      funext y; simp only [cf, List.map_cons, List.sum_cons]
    rw [h1]
    constructor
    · refine ContDiff.add ?_ ih1
      by_cases hc : p.1 = List.ofFn w
      · simp only [if_pos hc]; exact hp.2.1
      · simp only [if_neg hc]; exact contDiff_const
    · intro y hy
      show (if p.1 = List.ofFn w then p.2 y else 0) + cf L n w y = 0
      rw [ih2 y hy]
      by_cases hc : p.1 = List.ofFn w
      · simp [if_pos hc, hp.2.2 y hy]
      · simp [if_neg hc]

theorem single_term {m : ℕ} (p : List (Fin d) × (E d → ℂ)) (hp : p.1.length < m) (g : E d → ℂ) (y : E d) :
    ∑ n ∈ Finset.range m, ∑ w : Fin n → Fin d,
      (if p.1 = List.ofFn w then p.2 y else 0) * dw (List.ofFn w) g y = p.2 y * dw p.1 g y := by
  obtain ⟨v, c⟩ := p
  dsimp only at hp ⊢
  have key : ∀ (n : ℕ) (w : Fin n → Fin d), (if v = List.ofFn w then c y else 0) * ZetaZeros.D.EllReg.dw (List.ofFn w) g y
      = if v = List.ofFn w then c y * ZetaZeros.D.EllReg.dw v g y else 0 := by
    intro n w
    by_cases h : v = List.ofFn w
    · rw [if_pos h, if_pos h, h]
    · rw [if_neg h, if_neg h, zero_mul]
  simp only [key]
  rw [Finset.sum_eq_single v.length]
  · rw [Finset.sum_eq_single v.get]
    · rw [if_pos (List.ofFn_get v).symm]
    · intro w _ hw
      rw [if_neg]
      intro h
      apply hw
      have h' : List.ofFn w = List.ofFn v.get := by rw [← h, List.ofFn_get]
      exact List.ofFn_injective h'
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro n _ hn
    apply Finset.sum_eq_zero
    intro w _
    rw [if_neg]
    intro h
    apply hn
    rw [h, List.length_ofFn]
  · intro h
    exact absurd (Finset.mem_range.mpr hp) h

theorem ev_eq_cf {m : ℕ} (g : E d → ℂ) (y : E d) : ∀ L : List (List (Fin d) × (E d → ℂ)),
    (∀ p ∈ L, p.1.length < m) →
    ev L g y = ∑ n ∈ Finset.range m, ∑ w : Fin n → Fin d, cf L n w y * dw (List.ofFn w) g y
  | [], _ => by simp [ev, cf]
  | p :: L, hL => by
    rw [ev_cons, ev_eq_cf g y L (fun q hq => hL q (by simp [hq])), ← single_term p (hL p (by simp)) g y,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro n _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro w _
    simp only [cf, List.map_cons, List.sum_cons]
    ring

theorem dw_congr {F G : E d → ℂ} : ∀ (v : List (Fin d)) (y : E d), F =ᶠ[𝓝 y] G → dw v F =ᶠ[𝓝 y] dw v G
  | [], _, h => h
  | k :: v, y, h => by
    have ih : dw v F =ᶠ[𝓝 y] dw v G := dw_congr v y h
    filter_upwards [ih.eventuallyEq_nhds] with x hx
    simp only [dw_cons, Dk, hx.fderiv_eq]

theorem contDiff_ofReal' {χ : E d → ℝ} (hχ : ContDiff ℝ ∞ χ) : ContDiff ℝ ∞ (fun y => (χ y : ℂ)) := by
  have h := Complex.ofRealCLM.contDiff.comp hχ
  have e : (Complex.ofRealCLM ∘ χ) = fun y => (χ y : ℂ) := by
    funext y; simp
  rw [e] at h
  exact h

theorem smooth_cut {U : Set (E d)} (hU : IsOpen U) {a : E d → ℂ} (ha : ContDiffOn ℝ ∞ a U)
    {χ : E d → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχU : tsupport χ ⊆ U) :
    ContDiff ℝ ∞ (fun y => (χ y : ℂ) * a y) := by
  have hz0 : ∀ z, z ∉ tsupport χ → χ z = 0 := fun z hz => by
    by_contra h
    exact hz (subset_tsupport χ (Function.mem_support.mpr h))
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ U
  · exact (contDiff_ofReal' hχ).contDiffAt.mul (ha.contDiffAt (hU.mem_nhds hx))
  · have hxs : x ∉ tsupport χ := fun h => hx (hχU h)
    have hev : (fun y => (χ y : ℂ) * a y) =ᶠ[𝓝 x] fun _ => (0 : ℂ) := by
      filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hxs] with z hz
      simp [hz0 z hz]
    exact contDiffAt_const.congr_of_eventuallyEq hev

theorem intg {U K : Set (E d)} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) {u F : E d → ℂ}
    (hu : ContinuousOn u U) (hF : Continuous F) (hFK : ∀ y ∉ K, F y = 0) :
    Integrable (fun y => u y * F y) := by
  have hKc : IsClosed K := hK.isClosed
  have hcont : Continuous (fun y => u y * F y) := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x ∈ U
    · exact (hu.continuousAt (hU.mem_nhds hx)).mul hF.continuousAt
    · have hxK : x ∉ K := fun h => hx (hKU h)
      have hev : (fun _ => (0 : ℂ)) =ᶠ[𝓝 x] fun y => u y * F y := by
        filter_upwards [hKc.isOpen_compl.mem_nhds hxK] with z hz
        simp [hFK z hz]
      exact continuousAt_const.congr hev
  have hcs : HasCompactSupport (fun y => u y * F y) := by
    apply HasCompactSupport.intro hK
    intro y hy
    simp [hFK y hy]
  exact hcont.integrable_of_hasCompactSupport hcs

theorem swap4 {α : Type*} [AddCommMonoid α] (s t : Finset ℕ)
    (f : (n : ℕ) → (Fin n → Fin d) → (n' : ℕ) → (Fin n' → Fin d) → α) :
    ∑ n ∈ s, ∑ w : Fin n → Fin d, ∑ n' ∈ t, ∑ w' : Fin n' → Fin d, f n w n' w' =
      ∑ n' ∈ t, ∑ w' : Fin n' → Fin d, ∑ n ∈ s, ∑ w : Fin n → Fin d, f n w n' w' := by
  calc ∑ n ∈ s, ∑ w : Fin n → Fin d, ∑ n' ∈ t, ∑ w' : Fin n' → Fin d, f n w n' w'
      = ∑ n ∈ s, ∑ n' ∈ t, ∑ w' : Fin n' → Fin d, ∑ w : Fin n → Fin d, f n w n' w' := by
        refine Finset.sum_congr rfl (fun n _ => ?_)
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun n' _ => Finset.sum_comm)
    _ = ∑ n' ∈ t, ∑ n ∈ s, ∑ w' : Fin n' → Fin d, ∑ w : Fin n → Fin d, f n w n' w' := Finset.sum_comm
    _ = ∑ n' ∈ t, ∑ w' : Fin n' → Fin d, ∑ n ∈ s, ∑ w : Fin n → Fin d, f n w n' w' :=
        Finset.sum_congr rfl (fun n' _ => Finset.sum_comm)

private theorem formalAdjoint_mul_expand_lemma_3 {m : ℕ} {B : (n : ℕ) → (Fin n → Fin d) → ZetaZeros.D.EllReg.E d → ℂ}
    (hB : ∀ n w, ContDiff ℝ ∞ (B n w)) {a φ : ZetaZeros.D.EllReg.E d → ℂ} (ha : ContDiff ℝ ∞ a) (hφ : ContDiff ℝ ∞ φ) (y : ZetaZeros.D.EllReg.E d) :
    ZetaZeros.D.EllReg.trOp m B (fun z => a z * φ z) y = a y * ZetaZeros.D.EllReg.trOp m B φ y +
      ∑ n ∈ Finset.range (m + 1), ∑ w : Fin n → Fin d,
        (-1 : ℂ) ^ n * ev (sb (B n w) (lb (List.ofFn w) a)) φ y := by
  have key : ∀ (n : ℕ) (w : Fin n → Fin d), ZetaZeros.D.EllReg.dw (List.ofFn w) (fun z => B n w z * (a z * φ z)) y =
      a y * ZetaZeros.D.EllReg.dw (List.ofFn w) (fun z => B n w z * φ z) y +
        ev (sb (B n w) (lb (List.ofFn w) a)) φ y := by
    intro n w
    have e1 : (fun z => B n w z * (a z * φ z)) = fun z => a z * (B n w z * φ z) := by
      funext z; ring
    rw [e1, leib ha (List.ofFn w) _ ((hB n w).mul hφ)]
    simp only [ev_sb (hB n w) hφ y]
  simp only [ZetaZeros.D.EllReg.trOp, key, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro n _
  apply Finset.sum_congr rfl; intro w _
  ring

private theorem continuous_formalAdjoint_lemma_4 {m : ℕ} {B : (n : ℕ) → (Fin n → Fin d) → ZetaZeros.D.EllReg.E d → ℂ}
    (hB : ∀ n w, ContDiff ℝ ∞ (B n w)) {φ : ZetaZeros.D.EllReg.E d → ℂ} (hφ : ContDiff ℝ ∞ φ) :
    Continuous (ZetaZeros.D.EllReg.trOp m B φ) := by
  have e : ZetaZeros.D.EllReg.trOp m B φ = fun x => ∑ n ∈ Finset.range (m + 1), ∑ w : Fin n → Fin d,
      (-1 : ℂ) ^ n * ZetaZeros.D.EllReg.dw (List.ofFn w) (fun y => B n w y * φ y) x := by
    funext x; rfl
  rw [e]
  refine continuous_finsetSum _ (fun n _ => continuous_finsetSum _ (fun w _ => ?_))
  exact continuous_const.mul (contDiff_dw ((hB n w).mul hφ) _).continuous

private theorem formalAdjoint_congr_at_lemma_5 {m : ℕ} {b b' : (n : ℕ) → (Fin n → Fin d) → ZetaZeros.D.EllReg.E d → ℂ} {φ : ZetaZeros.D.EllReg.E d → ℂ}
    {y : ZetaZeros.D.EllReg.E d} (h : ∀ n w, b n w =ᶠ[𝓝 y] b' n w) : ZetaZeros.D.EllReg.trOp m b φ y = ZetaZeros.D.EllReg.trOp m b' φ y := by
  unfold ZetaZeros.D.EllReg.trOp
  apply Finset.sum_congr rfl; intro n _
  apply Finset.sum_congr rfl; intro w _
  congr 1
  apply Filter.EventuallyEq.eq_of_nhds
  apply dw_congr
  filter_upwards [h n w] with z hz
  rw [hz]

theorem contDiff_eF (ξ : E d) : ContDiff ℝ ∞ (eF ξ) := by
  have h1 : ContDiff ℝ ∞ (fun y : ZetaZeros.D.EllReg.E d => (inner ℝ y ξ : ℝ)) := by
    exact contDiff_id.inner ℝ contDiff_const
  have h2 := contDiff_ofReal' h1
  have h3 : ContDiff ℝ ∞ (fun y : ZetaZeros.D.EllReg.E d => -(2 * Real.pi * Complex.I * ((inner ℝ y ξ : ℝ) : ℂ))) :=
    (contDiff_const.mul h2).neg
  exact h3.cexp

end WF

open WF in
theorem weakEquationFourier : WeakFourier := by
  intro d ι _ P U u hE i χ χ' hχ hχc hχU hχ' hχ'c hχ'U hχχ'
  obtain ⟨hU, hcoef, -, hu, hweak⟩ := hE
  have hKcl : IsClosed (tsupport χ) := isClosed_tsupport χ
  have hKc : IsCompact (tsupport χ) := hχc.isCompact
  have hz0 : ∀ z, z ∉ tsupport χ → χ z = 0 := fun z hz => by
    by_contra h
    exact hz (subset_tsupport χ (Function.mem_support.mpr h))
  have hone : ∀ z ∈ tsupport χ, χ' z = 1 := fun z hz => (hχχ' z hz).eq_of_nhds
  obtain ⟨a, ha_def⟩ : ∃ a : E d → ℂ, a = fun z => (χ z : ℂ) := ⟨_, rfl⟩
  have ha : ContDiff ℝ ∞ a := by rw [ha_def]; exact ZetaZeros.D.EllReg.WF.contDiff_ofReal' hχ
  have haK : ∀ z ∉ tsupport χ, a z = 0 := fun z hz => by rw [ha_def]; simp [hz0 z hz]
  obtain ⟨B, hB_def⟩ : ∃ B : (n : ℕ) → (Fin n → Fin d) → E d → ℂ,
      B = fun n w z => (χ' z : ℂ) * P.a i n w z := ⟨_, rfl⟩
  have hB : ∀ n w, ContDiff ℝ ∞ (B n w) := by
    intro n w; rw [hB_def]; exact ZetaZeros.D.EllReg.WF.smooth_cut hU (hcoef i n w) hχ' hχ'U
  have hBev : ∀ y ∈ tsupport χ, ∀ n w, P.a i n w =ᶠ[𝓝 y] B n w := by
    intro y hy n w
    filter_upwards [hχχ' y hy] with z hz
    rw [hB_def]; simp [hz]
  have hMadm : ∀ n ∈ Finset.range (P.ord i + 1), ∀ w : Fin n → Fin d,
      ZetaZeros.D.EllReg.WF.Good (P.ord i) (tsupport χ) (ZetaZeros.D.EllReg.WF.sb (B n w) (ZetaZeros.D.EllReg.WF.lb (List.ofFn w) a)) := by
    intro n hn w
    have h1 := ZetaZeros.D.EllReg.WF.sb_good (hB n w) _ (ZetaZeros.D.EllReg.WF.lb_good ha hKcl haK (List.ofFn w))
    rw [List.length_ofFn] at h1
    have hn' : n ≤ P.ord i := by have := Finset.mem_range.mp hn; omega
    exact (ZetaZeros.D.EllReg.WF.good_mono h1) hn'
  obtain ⟨c, hc_def⟩ : ∃ c : (n : ℕ) → (Fin n → Fin d) → E d → ℂ, c = fun n' w' y =>
      -∑ n ∈ Finset.range (P.ord i + 1), ∑ w : Fin n → Fin d,
        (-1 : ℂ) ^ n * ZetaZeros.D.EllReg.WF.cf (ZetaZeros.D.EllReg.WF.sb (B n w) (ZetaZeros.D.EllReg.WF.lb (List.ofFn w) a)) n' w' y := ⟨_, rfl⟩
  have hc : ∀ n' (w' : Fin n' → Fin d), ContDiff ℝ ∞ (c n' w') := by
    intro n' w'
    rw [hc_def]
    apply ContDiff.neg
    apply ContDiff.sum; intro n hn
    apply ContDiff.sum; intro w _
    exact contDiff_const.mul (ZetaZeros.D.EllReg.WF.cf_good (hMadm n hn w) n' w').1
  have hc0 : ∀ n' (w' : Fin n' → Fin d), ∀ y ∉ tsupport χ, c n' w' y = 0 := by
    intro n' w' y hy
    simp only [hc_def, neg_eq_zero]
    apply Finset.sum_eq_zero; intro n hn
    apply Finset.sum_eq_zero; intro w _
    rw [(ZetaZeros.D.EllReg.WF.cf_good (hMadm n hn w) n' w').2 y hy, mul_zero]
  refine ⟨c, fun n' w' => ⟨hc n' w', HasCompactSupport.intro hKc (hc0 n' w')⟩, fun ξ => ?_⟩
  have hφ := ZetaZeros.D.EllReg.WF.contDiff_eF ξ
  obtain ⟨ψ, hψ_def⟩ : ∃ ψ : E d → ℂ, ψ = fun z => a z * eF ξ z := ⟨_, rfl⟩
  have hψs : ContDiff ℝ ∞ ψ := by rw [hψ_def]; exact ha.mul hφ
  have hψc : HasCompactSupport ψ :=
    HasCompactSupport.intro hKc (fun z hz => by rw [hψ_def]; simp [haK z hz])
  have hψU : tsupport ψ ⊆ U := by
    refine subset_trans ?_ hχU
    refine closure_minimal ?_ hKcl
    intro z hz
    by_contra hzK
    exact (Function.mem_support.mp hz) (by rw [hψ_def]; simp [haK z hzK])
  have hint_r : ∫ x, u x * P.tr i ψ x = 0 := hweak i ψ hψs hψc hψU
  have hψB : ∀ y, P.tr i ψ y = trOp (P.ord i) B ψ y := by
    intro y
    show trOp (P.ord i) (P.a i) ψ y = _
    unfold trOp
    apply Finset.sum_congr rfl; intro n _
    apply Finset.sum_congr rfl; intro w _
    have e : (fun z => P.a i n w z * ψ z) = fun z => B n w z * ψ z := by
      funext z
      by_cases hz : z ∈ tsupport χ
      · rw [hB_def]; simp [hone z hz]
      · rw [hψ_def]; simp [haK z hz]
    rw [e]
  have hL : ∀ y, cut χ u y * P.tr i (eF ξ) y =
      u y * (a y * trOp (P.ord i) B (eF ξ) y) := by
    intro y
    by_cases hy : y ∈ tsupport χ
    · have e : P.tr i (eF ξ) y = trOp (P.ord i) B (eF ξ) y := by
        show trOp (P.ord i) (P.a i) (eF ξ) y = _
        exact _root_.ZetaZeros.D.EllReg.WF.formalAdjoint_congr_at_lemma_5 (hBev y hy)
      rw [e, ha_def]
      simp only [cut]
      ring
    · have h0 : χ y = 0 := hz0 y hy
      rw [ha_def]
      simp [cut, h0]
  have hR : ∀ y, ∑ n ∈ Finset.range (P.ord i + 1), ∑ w : Fin n → Fin d,
      (-1 : ℂ) ^ n * ZetaZeros.D.EllReg.WF.ev (ZetaZeros.D.EllReg.WF.sb (B n w) (ZetaZeros.D.EllReg.WF.lb (List.ofFn w) a)) (eF ξ) y =
      -∑ n' ∈ Finset.range (P.ord i), ∑ w' : Fin n' → Fin d,
        c n' w' y * dw (List.ofFn w') (eF ξ) y := by
    intro y
    have h1 : ∀ n ∈ Finset.range (P.ord i + 1), ∀ w : Fin n → Fin d,
        (-1 : ℂ) ^ n * ZetaZeros.D.EllReg.WF.ev (ZetaZeros.D.EllReg.WF.sb (B n w) (ZetaZeros.D.EllReg.WF.lb (List.ofFn w) a)) (eF ξ) y =
        ∑ n' ∈ Finset.range (P.ord i), ∑ w' : Fin n' → Fin d,
          (-1 : ℂ) ^ n * (ZetaZeros.D.EllReg.WF.cf (ZetaZeros.D.EllReg.WF.sb (B n w) (ZetaZeros.D.EllReg.WF.lb (List.ofFn w) a)) n' w' y *
            dw (List.ofFn w') (eF ξ) y) := by
      intro n hn w
      rw [ZetaZeros.D.EllReg.WF.ev_eq_cf (eF ξ) y _ (fun p hp => (hMadm n hn w p hp).1), Finset.mul_sum]
      apply Finset.sum_congr rfl; intro n' _
      rw [Finset.mul_sum]
    calc ∑ n ∈ Finset.range (P.ord i + 1), ∑ w : Fin n → Fin d,
          (-1 : ℂ) ^ n * ZetaZeros.D.EllReg.WF.ev (ZetaZeros.D.EllReg.WF.sb (B n w) (ZetaZeros.D.EllReg.WF.lb (List.ofFn w) a)) (eF ξ) y
        = ∑ n ∈ Finset.range (P.ord i + 1), ∑ w : Fin n → Fin d,
            ∑ n' ∈ Finset.range (P.ord i), ∑ w' : Fin n' → Fin d,
              (-1 : ℂ) ^ n * (ZetaZeros.D.EllReg.WF.cf (ZetaZeros.D.EllReg.WF.sb (B n w) (ZetaZeros.D.EllReg.WF.lb (List.ofFn w) a)) n' w' y *
                dw (List.ofFn w') (eF ξ) y) := by
          apply Finset.sum_congr rfl; intro n hn
          apply Finset.sum_congr rfl; intro w _
          exact h1 n hn w
      _ = ∑ n' ∈ Finset.range (P.ord i), ∑ w' : Fin n' → Fin d,
            ∑ n ∈ Finset.range (P.ord i + 1), ∑ w : Fin n → Fin d,
              (-1 : ℂ) ^ n * (ZetaZeros.D.EllReg.WF.cf (ZetaZeros.D.EllReg.WF.sb (B n w) (ZetaZeros.D.EllReg.WF.lb (List.ofFn w) a)) n' w' y *
                dw (List.ofFn w') (eF ξ) y) := ZetaZeros.D.EllReg.WF.swap4 _ _ _
      _ = -∑ n' ∈ Finset.range (P.ord i), ∑ w' : Fin n' → Fin d,
            c n' w' y * dw (List.ofFn w') (eF ξ) y := by
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl; intro n' _
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl; intro w' _
          rw [hc_def]
          simp only [Finset.sum_mul, neg_mul, neg_neg, mul_assoc]
  have hpt : ∀ y, u y * P.tr i ψ y = u y * (a y * trOp (P.ord i) B (eF ξ) y) -
      ∑ n' ∈ Finset.range (P.ord i), ∑ w' : Fin n' → Fin d,
        u y * (c n' w' y * dw (List.ofFn w') (eF ξ) y) := by
    intro y
    rw [hψB y, hψ_def, _root_.ZetaZeros.D.EllReg.WF.formalAdjoint_mul_expand_lemma_3 hB ha hφ y, hR y, mul_add, mul_neg, sub_eq_add_neg,
      Finset.mul_sum]
    congr 2
    apply Finset.sum_congr rfl; intro n' _
    rw [Finset.mul_sum]
  have hG : Integrable (fun y => u y * (a y * trOp (P.ord i) B (eF ξ) y)) :=
    ZetaZeros.D.EllReg.WF.intg hU hKc hχU hu
      (ha.continuous.mul (_root_.ZetaZeros.D.EllReg.WF.continuous_formalAdjoint_lemma_4 hB hφ)) (fun y hy => by simp [haK y hy])
  have hH : ∀ n' (w' : Fin n' → Fin d),
      Integrable (fun y => u y * (c n' w' y * dw (List.ofFn w') (eF ξ) y)) :=
    fun n' w' => ZetaZeros.D.EllReg.WF.intg hU hKc hχU hu
      ((hc n' w').continuous.mul (ZetaZeros.D.EllReg.WF.contDiff_dw hφ _).continuous) (fun y hy => by simp [hc0 n' w' y hy])
  have hmain : ∫ y, u y * (a y * trOp (P.ord i) B (eF ξ) y) =
      ∑ n' ∈ Finset.range (P.ord i), ∑ w' : Fin n' → Fin d,
        ∫ y, u y * (c n' w' y * dw (List.ofFn w') (eF ξ) y) := by
    have e := hint_r
    rw [show (fun x => u x * P.tr i ψ x) = fun y =>
        u y * (a y * trOp (P.ord i) B (eF ξ) y) -
          ∑ n' ∈ Finset.range (P.ord i), ∑ w' : Fin n' → Fin d,
            u y * (c n' w' y * dw (List.ofFn w') (eF ξ) y) from funext hpt] at e
    rw [integral_sub hG (integrable_finsetSum _ fun n' _ => integrable_finsetSum _ fun w' _ => hH n' w'),
      integral_finsetSum _ (fun n' _ => integrable_finsetSum _ fun w' _ => hH n' w')] at e
    have e2 : ∀ n' ∈ Finset.range (P.ord i), ∫ y, ∑ w' : Fin n' → Fin d,
        u y * (c n' w' y * dw (List.ofFn w') (eF ξ) y) =
        ∑ w' : Fin n' → Fin d, ∫ y, u y * (c n' w' y * dw (List.ofFn w') (eF ξ) y) :=
      fun n' _ => integral_finsetSum _ (fun w' _ => hH n' w')
    rw [Finset.sum_congr rfl e2] at e
    exact sub_eq_zero.mp e
  calc ∫ y, cut χ u y * P.tr i (eF ξ) y
      = ∫ y, u y * (a y * trOp (P.ord i) B (eF ξ) y) := by
        congr 1; funext y; exact hL y
    _ = ∑ n' ∈ Finset.range (P.ord i), ∑ w' : Fin n' → Fin d,
          ∫ y, u y * (c n' w' y * dw (List.ofFn w') (eF ξ) y) := hmain
    _ = ∑ n' ∈ Finset.range (P.ord i), ∑ w' : Fin n' → Fin d,
          ∫ y, cut χ' u y * c n' w' y * dw (List.ofFn w') (eF ξ) y := by
        apply Finset.sum_congr rfl; intro n' _
        apply Finset.sum_congr rfl; intro w' _
        congr 1; funext y
        by_cases hy : y ∈ tsupport χ
        · simp only [cut, hone y hy, Complex.ofReal_one]
          ring
        · rw [hc0 n' w' y hy]
          simp

end

end ZetaZeros.D.EllReg
end

section -- merged from Formalism.UnipotentAdelicQuotients.EllipticRegularity.ConvolutionBound
namespace ZetaZeros.D.EllReg

open MeasureTheory
open scoped ENNReal

variable {d : ℕ}

private lemma conv_sq_le (k g : E d → ℝ≥0∞) (hk : Measurable k) (hg : Measurable g) (ξ : E d) :
    (∫⁻ η, k (ξ - η) * g η) ^ 2 ≤ (∫⁻ ζ, k ζ) * ∫⁻ η, k (ξ - η) * g η ^ 2 := by
  first | exact UpperTheory.Reformulated.B.Qj8.conv_sq_le .. | (apply UpperTheory.Reformulated.B.Qj8.conv_sq_le <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qj8.conv_sq_le <;> assumption) | (apply @UpperTheory.Reformulated.B.Qj8.conv_sq_le <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qj8.conv_sq_le <;> assumption) | (apply @UpperTheory.Reformulated.B.Qj8.conv_sq_le <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.Qj8.conv_sq_le d k g hk hg ξ | exact @UpperTheory.Reformulated.B.Qj8.conv_sq_le d k g hk hg | exact @UpperTheory.Reformulated.B.Qj8.conv_sq_le d k g hk | exact @UpperTheory.Reformulated.B.Qj8.conv_sq_le d k g | exact @UpperTheory.Reformulated.B.Qj8.conv_sq_le d k | exact @UpperTheory.Reformulated.B.Qj8.conv_sq_le d

private lemma conv_young (k g : E d → ℝ≥0∞) (hk : Measurable k) (hg : Measurable g) :
    ∫⁻ ξ, (∫⁻ η, k (ξ - η) * g η) ^ 2 ≤ (∫⁻ ζ, k ζ) ^ 2 * ∫⁻ η, g η ^ 2 := by
  have hm : Measurable (Function.uncurry fun ξ η : E d => k (ξ - η) * g η ^ 2) :=
    (hk.comp (measurable_fst.sub measurable_snd)).mul ((hg.comp measurable_snd).pow_const 2)
  calc ∫⁻ ξ, (∫⁻ η, k (ξ - η) * g η) ^ 2
      ≤ ∫⁻ ξ, (∫⁻ ζ, k ζ) * ∫⁻ η, k (ξ - η) * g η ^ 2 := lintegral_mono fun ξ => conv_sq_le k g hk hg ξ
    _ = (∫⁻ ζ, k ζ) * ∫⁻ ξ, ∫⁻ η, k (ξ - η) * g η ^ 2 :=
      lintegral_const_mul _ hm.lintegral_prod_right'
    _ = (∫⁻ ζ, k ζ) * ∫⁻ η, ∫⁻ ξ, k (ξ - η) * g η ^ 2 := by
      rw [lintegral_lintegral_swap hm.aemeasurable]
    _ = (∫⁻ ζ, k ζ) * ∫⁻ η, (∫⁻ ζ, k ζ) * g η ^ 2 := by
      congr 1
      refine lintegral_congr fun η => ?_
      rw [lintegral_mul_const _ (show Measurable fun ξ => k (ξ - η) from hk.comp (measurable_id.sub measurable_const)),
        lintegral_sub_right_eq_self k η]
    _ = (∫⁻ ζ, k ζ) ^ 2 * ∫⁻ η, g η ^ 2 := by
      rw [lintegral_const_mul _ (hg.pow_const 2)]; ring

private lemma om_measurable (s M ε : ℝ) : Measurable (om (d := d) s M ε) := by
  unfold om; fun_prop

theorem convolution_bound : ConvBound := by
  intro d s M ε C N hC hom K F hK hF
  have hKm : Measurable K := hK.measurable
  have hFm : Measurable F := hF.measurable
  obtain ⟨k1, hk1e⟩ : ∃ k1 : E d → ℝ≥0∞, k1 = fun ζ => ‖K ζ‖ₑ := ⟨_, rfl⟩
  obtain ⟨k3, hk3e⟩ : ∃ k3 : E d → ℝ≥0∞, k3 = fun ζ => ENNReal.ofReal (‖ζ‖ * (1 + ‖ζ‖) ^ N) * ‖K ζ‖ₑ :=
    ⟨_, rfl⟩
  obtain ⟨k2, hk2e⟩ : ∃ k2 : E d → ℝ≥0∞, k2 = fun ζ => ENNReal.ofReal C * k3 ζ := ⟨_, rfl⟩
  obtain ⟨g1, hg1e⟩ : ∃ g1 : E d → ℝ≥0∞, g1 = fun η => ENNReal.ofReal (om s M ε η) * ‖F η‖ₑ := ⟨_, rfl⟩
  obtain ⟨g2, hg2e⟩ : ∃ g2 : E d → ℝ≥0∞, g2 = fun η => ENNReal.ofReal (om (s - 1) M ε η) * ‖F η‖ₑ :=
    ⟨_, rfl⟩
  have hk1 : Measurable k1 := by rw [hk1e]; exact hKm.enorm
  have hk3 : Measurable k3 := by
    rw [hk3e]
    exact (ENNReal.measurable_ofReal.comp (by fun_prop)).mul hKm.enorm
  have hk2 : Measurable k2 := by rw [hk2e]; exact measurable_const.mul hk3
  have hg1 : Measurable g1 := by
    rw [hg1e]; exact (ENNReal.measurable_ofReal.comp (om_measurable s M ε)).mul hFm.enorm
  have hg2 : Measurable g2 := by
    rw [hg2e]; exact (ENNReal.measurable_ofReal.comp (om_measurable (s - 1) M ε)).mul hFm.enorm
  have hprod : ∀ k g : E d → ℝ≥0∞, Measurable k → Measurable g →
      Measurable (Function.uncurry fun ξ η : E d => k (ξ - η) * g η) := fun k g hk hg =>
    (hk.comp (measurable_fst.sub measurable_snd)).mul (hg.comp measurable_snd)
  have hT1 : Measurable fun ξ => ∫⁻ η, k1 (ξ - η) * g1 η := (hprod k1 g1 hk1 hg1).lintegral_prod_right'
  have hT2 : Measurable fun ξ => ∫⁻ η, k2 (ξ - η) * g2 η := (hprod k2 g2 hk2 hg2).lintegral_prod_right'

  have hpt : ∀ ξ, ENNReal.ofReal (om s M ε ξ) * ‖conv K F ξ‖ₑ ≤
      (∫⁻ η, k1 (ξ - η) * g1 η) + ∫⁻ η, k2 (ξ - η) * g2 η := by
    intro ξ
    have h1 : ‖conv K F ξ‖ₑ ≤ ∫⁻ η, ‖K (ξ - η)‖ₑ * ‖F η‖ₑ := by
      unfold conv
      refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
      refine lintegral_congr fun η => ?_
      rw [enorm_mul]
    have hmeas : Measurable fun η => k1 (ξ - η) * g1 η :=
      (hk1.comp (measurable_const.sub measurable_id)).mul hg1
    calc ENNReal.ofReal (om s M ε ξ) * ‖conv K F ξ‖ₑ
        ≤ ENNReal.ofReal (om s M ε ξ) * ∫⁻ η, ‖K (ξ - η)‖ₑ * ‖F η‖ₑ := by gcongr
      _ = ∫⁻ η, ENNReal.ofReal (om s M ε ξ) * (‖K (ξ - η)‖ₑ * ‖F η‖ₑ) :=
        (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
      _ ≤ ∫⁻ η, (k1 (ξ - η) * g1 η + k2 (ξ - η) * g2 η) := by
        refine lintegral_mono fun η => ?_
        have hr : om s M ε ξ ≤ om s M ε η + C * ‖ξ - η‖ * (1 + ‖ξ - η‖) ^ N * om (s - 1) M ε η := by
          have h := hom ξ η
          have h' := le_abs_self (om s M ε ξ - om s M ε η)
          linarith
        have hX : 0 ≤ ‖ξ - η‖ * (1 + ‖ξ - η‖) ^ N := by positivity
        have hY := om_nonneg (s - 1) M ε η
        have he : ENNReal.ofReal (om s M ε ξ) ≤ ENNReal.ofReal (om s M ε η) +
            ENNReal.ofReal C * (ENNReal.ofReal (‖ξ - η‖ * (1 + ‖ξ - η‖) ^ N) *
              ENNReal.ofReal (om (s - 1) M ε η)) := by
          rw [← ENNReal.ofReal_mul hX, ← ENNReal.ofReal_mul hC,
            ← ENNReal.ofReal_add (om_nonneg s M ε η) (by positivity)]
          exact ENNReal.ofReal_le_ofReal (le_of_le_of_eq hr (by ring))
        calc ENNReal.ofReal (om s M ε ξ) * (‖K (ξ - η)‖ₑ * ‖F η‖ₑ)
            ≤ (ENNReal.ofReal (om s M ε η) + ENNReal.ofReal C * (ENNReal.ofReal (‖ξ - η‖ * (1 + ‖ξ - η‖) ^ N) *
              ENNReal.ofReal (om (s - 1) M ε η))) * (‖K (ξ - η)‖ₑ * ‖F η‖ₑ) := by gcongr
          _ = k1 (ξ - η) * g1 η + k2 (ξ - η) * g2 η := by
            rw [hk1e, hk2e, hk3e, hg1e, hg2e]; ring
      _ = (∫⁻ η, k1 (ξ - η) * g1 η) + ∫⁻ η, k2 (ξ - η) * g2 η := lintegral_add_left hmeas _
  have hn : nrm s M ε (conv K F) ≤
      ∫⁻ ξ, ((∫⁻ η, k1 (ξ - η) * g1 η) + ∫⁻ η, k2 (ξ - η) * g2 η) ^ (2 : ℝ) := by
    unfold nrm
    refine lintegral_mono fun ξ => ?_
    rw [ENNReal.rpow_two, ← mul_pow]
    gcongr
    exact hpt ξ
  have hY : ∀ (k g : E d → ℝ≥0∞), Measurable k → Measurable g →
      (∫⁻ ξ, (∫⁻ η, k (ξ - η) * g η) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) ≤
        (∫⁻ ζ, k ζ) * (∫⁻ η, g η ^ 2) ^ (1 / 2 : ℝ) := by
    intro k g hk hg
    have h := conv_young k g hk hg
    simp only [← ENNReal.rpow_two] at h ⊢
    calc (∫⁻ ξ, (∫⁻ η, k (ξ - η) * g η) ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
        ≤ ((∫⁻ ζ, k ζ) ^ (2 : ℝ) * ∫⁻ η, g η ^ (2 : ℝ)) ^ (1 / 2 : ℝ) :=
          ENNReal.rpow_le_rpow h (by norm_num)
      _ = (∫⁻ ζ, k ζ) * (∫⁻ η, g η ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul]; norm_num
  have e1 : ∫⁻ η, g1 η ^ 2 = nrm s M ε F := by
    unfold nrm; rw [hg1e]; simp only [mul_pow]
  have e2 : ∫⁻ η, g2 η ^ 2 = nrm (s - 1) M ε F := by
    unfold nrm; rw [hg2e]; simp only [mul_pow]
  have e3 : ∫⁻ ζ, k2 ζ = ENNReal.ofReal C * ∫⁻ ζ, ENNReal.ofReal (‖ζ‖ * (1 + ‖ζ‖) ^ N) * ‖K ζ‖ₑ := by
    rw [hk2e, lintegral_const_mul _ hk3, hk3e]
  have e4 : ∫⁻ ζ, k1 ζ = ∫⁻ ζ, ‖K ζ‖ₑ := by rw [hk1e]
  have hMk := ENNReal.lintegral_Lp_add_le (μ := volume) (p := 2) hT1.aemeasurable hT2.aemeasurable
    (by norm_num)
  simp only [Pi.add_apply] at hMk
  calc nrm s M ε (conv K F) ^ (1 / 2 : ℝ)
      ≤ (∫⁻ ξ, ((∫⁻ η, k1 (ξ - η) * g1 η) + ∫⁻ η, k2 (ξ - η) * g2 η) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow hn (by norm_num)
    _ ≤ (∫⁻ ξ, (∫⁻ η, k1 (ξ - η) * g1 η) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) +
        (∫⁻ ξ, (∫⁻ η, k2 (ξ - η) * g2 η) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := hMk
    _ ≤ (∫⁻ ζ, k1 ζ) * (∫⁻ η, g1 η ^ 2) ^ (1 / 2 : ℝ) + (∫⁻ ζ, k2 ζ) * (∫⁻ η, g2 η ^ 2) ^ (1 / 2 : ℝ) :=
        add_le_add (hY k1 g1 hk1 hg1) (hY k2 g2 hk2 hg2)
    _ = _ := by rw [e1, e2, e3, e4]

end ZetaZeros.D.EllReg
end

namespace ZetaZeros.D.EllReg

theorem elliptic_regularity_of_parts : Internal := by
  have hSP : StepOfParts :=
    stepOfParts_of frozenDecompositionOfParts weightedNormFinite weightedNormLimit regularity_inductive_step
  exact internal_of_all smoothOfSobolevAll existsBump cutoffContinuous smoothOfLocallySmooth
    sobolevOfCompactSupport symbolLowerBound sobolevWeightLipschitz convolution_bound frozenKernelSmall
    adjointPairingFourier iteratedPartialFourierChar integralFourierChar adjointPairingLocal weakEquationFourier hSP

end ZetaZeros.D.EllReg
