module

public import Development.WeilBound.ThetaLifts.FrameEstimates.WeilConv
public import Development.WeilBound.ThetaLifts.CartanFactorisation.IntegrableOnRight
public import Development.WeilBound.ThetaLifts.CartanFactorisation.Unimod
public import Development.WeilBound.ThetaLifts.FrameEstimates.SchrAddPt
public import Development.WeilBound.ThetaLifts.FrameEstimates.CuspRapidOf

@[expose] public section

section -- merged from Development.WeilBound.ThetaLifts.FrameEstimates.IInvOfParts
noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

theorem topGroup_UA {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) : IsTopologicalGroup (UA σ J) := by
  have : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have : IsTopologicalGroup (GL (Fin n) (AE F E)) := inferInstance
  exact Subgroup.instIsTopologicalGroupSubtypeMem _

theorem iInv_of_parts (hB : ThetaBasic) (hU : PositivityTheory.ThKF.Unimod) (hE : EpsOf) : IInv := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp Φ hΦ
  have hi := ((hB F E σ B n d X W M χX χW om r s r' s' hp).1 Φ hΦ).2.1
  refine ⟨fun γ hγ h => ?_, fun g₀ => funext fun h => ?_, fun h h' => ?_⟩
  · simp only [Model.I]
    congr 1
    funext g
    simpa using hi 1 (one_mem _) γ hγ g h
  · obtain ⟨h1, -, h3⟩ := hU F E σ hp.base.cm n X.J 1 (fun i j => by simpa using hp.herm.herm i j)
      (hE F E σ B hp.base n X r s (Or.inl hp.herm)).1.2
    have := topGroup_UA σ X.J
    have := h3 _ hp.good.haar
    have := hp.good.haar
    have : BorelSpace (UA σ X.J) := ⟨rfl⟩
    have e : ∀ g, theta om (om (g₀, 1) Φ) g h = theta om Φ (g * g₀) h := fun g => by
      simp only [theta, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
    simp only [Model.I, e]
    exact PositivityTheory.ThKF.L2.integral_right hp.good.dom (fun g => theta om Φ g h)
      (fun γ hγ g => by simpa using hi γ hγ 1 (one_mem _) g h) g₀
  · simp only [Model.I, theta, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]

theorem iInv_of (hB : ThetaBasic) : IInv := iInv_of_parts hB PositivityTheory.ThKF.unimodularity_holds epsOf_of

end PositivityTheory.ThKEst

end
end

section -- merged from Development.WeilBound.ThetaLifts.FrameEstimates.LinDer
section -- merged from Development.WeilBound.ThetaLifts.FrameEstimates.LinDerA
noncomputable section

namespace PositivityTheory.ThKEst.LinDerPf

open Filter Topology Asymptotics

section Step

variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

theorem step (β : Multiplicative ℝ →* H) (hβ : Continuous β) (f f' : H → ℂ) (hf' : Continuous f')
    (hd : ∀ h, HasDerivAt (fun t : ℝ => f (h * β (Multiplicative.ofAdd t))) (f' h) 0)
    (p : ℝ → H) (hp : ContinuousAt p 0) (u : ℝ → ℝ) (u' : ℝ) (hu : HasDerivAt u u' 0) (hu0 : u 0 = 0)
    (D : ℂ) (hD : HasDerivAt (fun t => f (p t)) D 0) :
    HasDerivAt (fun t => f (p t * β (Multiplicative.ofAdd (u t)))) (D + u' * f' (p 0)) 0 := by
  have hd' : ∀ h (v : ℝ), HasDerivAt (fun t : ℝ => f (h * β (Multiplicative.ofAdd t)))
      (f' (h * β (Multiplicative.ofAdd v))) v := fun h v => by
    have h1 := hd (h * β (Multiplicative.ofAdd v))
    have h2 : HasDerivAt (fun t : ℝ => f (h * β (Multiplicative.ofAdd v) * β (Multiplicative.ofAdd t)))
        (f' (h * β (Multiplicative.ofAdd v))) (v - v) := by rwa [sub_self]
    have h3 := h2.comp_sub_const v v
    refine h3.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
    simp only [mul_assoc, ← map_mul, ← ofAdd_add, add_sub_cancel]
  set R : ℝ → ℂ := fun t => f (p t * β (Multiplicative.ofAdd (u t))) - f (p t) - u t * f' (p 0) with hR
  have hc : Continuous fun z : H × ℝ => f' (z.1 * β (Multiplicative.ofAdd z.2)) :=
    hf'.comp (continuous_fst.mul (hβ.comp (continuous_ofAdd.comp continuous_snd)))
  have ho : R =o[𝓝 0] u := by
    refine isLittleO_iff.2 fun ε hε => ?_
    have h1 : ∀ᶠ z : H × ℝ in 𝓝 (p 0, 0), ‖f' (z.1 * β (Multiplicative.ofAdd z.2)) - f' (p 0)‖ ≤ ε := by
      have h2 := (hc.tendsto (p 0, 0))
      simp only [ofAdd_zero, map_one, mul_one] at h2
      filter_upwards [h2 (Metric.closedBall_mem_nhds _ hε)] with z hz
      simpa [dist_eq_norm] using hz
    rw [nhds_prod_eq] at h1
    obtain ⟨U, hU, V, hV, hUV⟩ := Filter.eventually_prod_iff.1 h1
    obtain ⟨δ, hδ, hδV⟩ := Metric.eventually_nhds_iff_ball.1 hV
    have hu1 : ∀ᶠ t in 𝓝 (0 : ℝ), u t ∈ Metric.ball (0 : ℝ) δ := by
      have := hu.continuousAt.tendsto
      rw [hu0] at this
      exact this (Metric.ball_mem_nhds _ hδ)
    filter_upwards [hp.tendsto hU, hu1] with t ht1 ht2
    have h3 := (convex_ball (0 : ℝ) δ).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun v : ℝ => f (p t * β (Multiplicative.ofAdd v)) - v * f' (p 0))
      (f' := fun v : ℝ => f' (p t * β (Multiplicative.ofAdd v)) - f' (p 0)) (C := ε)
      (fun v _ => by
        have h4 : HasDerivAt (fun v : ℝ => (v : ℂ) * f' (p 0)) (f' (p 0)) v := by
          simpa using (Complex.ofRealCLM.hasDerivAt (x := v)).mul_const (f' (p 0))
        exact ((hd' (p t) v).sub h4).hasDerivWithinAt)
      (fun v hv => hUV ht1 (hδV v hv)) (Metric.mem_ball_self hδ) ht2
    simp only [ofAdd_zero, map_one, mul_one, Complex.ofReal_zero, zero_mul, sub_zero] at h3
    have e : R t = f (p t * β (Multiplicative.ofAdd (u t))) - u t * f' (p 0) - f (p t) := by
      simp only [hR]
      ring
    rw [e]
    exact h3
  have hO : u =O[𝓝 0] fun t : ℝ => t - 0 := by
    have := hu.isBigO_sub
    simpa [hu0] using this
  have hR0 : HasDerivAt R 0 0 := by
    rw [hasDerivAt_iff_isLittleO]
    have : R 0 = 0 := by simp [hR, hu0]
    simpa [this] using ho.trans_isBigO hO
  have h5 : HasDerivAt (fun t : ℝ => (u t : ℂ) * f' (p 0)) (u' * f' (p 0)) 0 :=
    hu.ofReal_comp.mul_const _
  have h6 := (hR0.add hD).add h5
  rw [zero_add] at h6
  refine h6.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
  simp only [hR, Pi.add_apply]
  ring

theorem chain (f : H → ℂ) : ∀ (m : ℕ) (β : Fin m → Multiplicative ℝ →* H) (_ : ∀ i, Continuous (β i))
    (f' : Fin m → H → ℂ) (_ : ∀ i, Continuous (f' i))
    (_ : ∀ i h, HasDerivAt (fun t : ℝ => f (h * β i (Multiplicative.ofAdd t))) (f' i h) 0)
    (p : ℝ → H) (_ : ContinuousAt p 0) (u : Fin m → ℝ → ℝ) (u' : Fin m → ℝ) (_ : ∀ i, HasDerivAt (u i) (u' i) 0)
    (_ : ∀ i, u i 0 = 0) (D : ℂ) (_ : HasDerivAt (fun t => f (p t)) D 0),
    HasDerivAt (fun t => f (p t * (List.ofFn fun i => β i (Multiplicative.ofAdd (u i t))).prod))
      (D + ∑ i, (u' i : ℂ) * f' i (p 0)) 0 := by
  intro m
  induction m with
  | zero =>
    intro β _ f' _ _ p _ u u' _ _ D hD
    simpa using hD
  | succ m ih =>
    intro β hβ f' hf' hd p hp u u' hu hu0 D hD
    have h1 := step (β 0) (hβ 0) f (f' 0) (hf' 0) (hd 0) p hp (u 0) (u' 0) (hu 0) (hu0 0) D hD
    have h2 := ih (fun i => β i.succ) (fun i => hβ _) (fun i => f' i.succ) (fun i => hf' _) (fun i => hd _)
      (fun t => p t * β 0 (Multiplicative.ofAdd (u 0 t)))
      (hp.mul (((hβ 0).comp continuous_ofAdd).continuousAt.comp (hu 0).continuousAt))
      (fun i => u i.succ) (fun i => u' i.succ) (fun i => hu _) (fun i => hu0 _) _ h1
    simp only [hu0, ofAdd_zero, map_one, mul_one] at h2
    simpa only [List.ofFn_succ, List.prod_cons, mul_assoc, Fin.sum_univ_succ, add_assoc] using h2

end Step

section Alg

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

def Gr (a : A →L[ℝ] A) (g : A) : Prop := a g * g = 1 ∧ g * a g = 1

def pr (a : A →L[ℝ] A) : A →L[ℝ] A := (1 / 2 : ℝ) • (ContinuousLinearMap.id ℝ A - a)

theorem pr_apply (a : A →L[ℝ] A) (x : A) : pr a x = (1 / 2 : ℝ) • (x - a x) := rfl

variable {a : A →L[ℝ] A}

theorem Gr.mul (ha : ∀ x y, a (x * y) = a y * a x) {g h : A} (hg : Gr a g) (hh : Gr a h) : Gr a (g * h) := by
  constructor
  · rw [ha, mul_assoc, ← mul_assoc (a g), hg.1, one_mul, hh.1]
  · rw [ha, mul_assoc, ← mul_assoc h, hh.2, one_mul, hg.2]

theorem Gr.list (ha : ∀ x y, a (x * y) = a y * a x) (h1 : a 1 = 1) (l : List A) (hl : ∀ g ∈ l, Gr a g) :
    Gr a l.prod := by
  induction l with
  | nil => simp [Gr, h1]
  | cons x l ih =>
    rw [List.prod_cons]
    exact (hl x (by simp)).mul ha (ih fun g hg => hl g (by simp [hg]))

theorem Gr.anti (ha : ∀ x y, a (x * y) = a y * a x) (h1 : a 1 = 1) {g : A} (hg : Gr a g) :
    a (pr a g) = -pr a g := by
  have h2 : a g * a (a g) = 1 := by rw [← ha, hg.1, h1]
  have h3 : a (a g) = g := by
    calc a (a g) = (g * a g) * a (a g) := by rw [hg.2, one_mul]
      _ = g := by rw [mul_assoc, h2, mul_one]
  rw [pr_apply, map_smul, map_sub, h3, ← smul_neg, neg_sub]

theorem Gr.eq_of_pr {g h : A} (hg : Gr a g) (hh : Gr a h) (h1 : ‖1 - a g‖ ≤ 1 / 2) (h2 : ‖1 - a h‖ ≤ 1 / 2)
    (e : pr a g = pr a h) : g = h := by
  have e1 : g - a g = h - a h := by
    have := congrArg (fun x => (2 : ℝ) • x) e
    simpa [pr_apply, smul_smul] using this
  set D := g - h with hD
  have e2 : a g * D * a h = -D := by
    rw [hD, mul_sub, sub_mul, hg.1, one_mul, mul_assoc, hh.2, mul_one]
    have : a h = h - (g - a g) := by rw [e1]; abel
    rw [this]; abel
  have e3 : (2 : ℝ) • D = (1 - a g) * D + D * (1 - a h) - (1 - a g) * D * (1 - a h) := by
    have : (1 - a g) * D + D * (1 - a h) - (1 - a g) * D * (1 - a h) = D - a g * D * a h := by noncomm_ring
    rw [this, e2, two_smul, sub_neg_eq_add]
  have n1 : ‖(1 - a g) * D‖ ≤ 1 / 2 * ‖D‖ := (norm_mul_le _ _).trans (by gcongr)
  have n2 : ‖D * (1 - a h)‖ ≤ ‖D‖ * (1 / 2) := (norm_mul_le _ _).trans (by gcongr)
  have n3 : ‖(1 - a g) * D * (1 - a h)‖ ≤ 1 / 2 * ‖D‖ * (1 / 2) := (norm_mul_le _ _).trans (by gcongr)
  have n4 : 2 * ‖D‖ ≤ ‖(1 - a g) * D‖ + ‖D * (1 - a h)‖ + ‖(1 - a g) * D * (1 - a h)‖ := by
    have : ‖(2 : ℝ) • D‖ = 2 * ‖D‖ := by rw [norm_smul]; norm_num
    rw [← this, e3]
    exact (norm_sub_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
  have : ‖D‖ ≤ 0 := by linarith
  exact sub_eq_zero.1 (norm_le_zero_iff.1 this)

theorem prod_strict : ∀ (m : ℕ) {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (e : Fin m → V → A)
    (e' : Fin m → V →L[ℝ] A) (_ : ∀ i, HasStrictFDerivAt (e i) (e' i) 0) (_ : ∀ i, e i 0 = 1),
    HasStrictFDerivAt (fun s => (List.ofFn fun i => e i s).prod) (∑ i, e' i) 0 := by
  intro m V _ _
  induction m with
  | zero =>
    intro e e' _ _
    simpa using hasStrictFDerivAt_const (1 : A) (0 : V)
  | succ m ih =>
    intro e e' he h0
    have h1 := (he 0).mul' (ih (fun i => e i.succ) (fun i => e' i.succ) (fun i => he _) (fun i => h0 _))
    have h2 : (List.ofFn fun i : Fin m => e i.succ 0).prod = 1 := by simp [h0]
    simp only [h2] at h1
    simp only [h0, one_smul, MulOpposite.op_one] at h1
    simp only [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ]
    rw [add_comm (e' 0)]
    exact h1

theorem coords (ha : ∀ x y, a (x * y) = a y * a x) (h1 : a 1 = 1) {m : ℕ} (Y : Fin m → A) (hY : ∀ i, a (Y i) = -Y i)
    (c : A →L[ℝ] (Fin m → ℝ)) (hc : ∀ s : Fin m → ℝ, c (∑ i, s i • Y i) = s)
    (hc' : ∀ x y, a x = -x → a y = -y → c x = c y → x = y)
    (e : Fin m → ℝ → A) (he : ∀ i, HasStrictDerivAt (e i) (Y i) 0) (he0 : ∀ i, e i 0 = 1) (heG : ∀ i t, Gr a (e i t))
    (g : ℝ → A) (Z : A) (hg : HasDerivAt g Z 0) (hg0 : g 0 = 1) (hgG : ∀ t, Gr a (g t)) :
    ∃ s : ℝ → Fin m → ℝ, s 0 = 0 ∧ HasDerivAt s (c (pr a Z)) 0 ∧
      ∀ᶠ t in 𝓝 (0 : ℝ), g t = (List.ofFn fun i => e i (s t i)).prod := by
  set Φ : (Fin m → ℝ) → A := fun s => (List.ofFn fun i => e i (s i)).prod with hΦ
  have hΦ0 : Φ 0 = 1 := by simp [hΦ, he0]
  have hΦG : ∀ s, Gr a (Φ s) := fun s => Gr.list ha h1 _ fun x hx => by
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hx
    exact heG _ _
  have hΦd : HasStrictFDerivAt Φ
      (∑ i, (ContinuousLinearMap.toSpanSingleton ℝ (Y i)).comp (ContinuousLinearMap.proj i)) 0 :=
    prod_strict m (fun i (s : Fin m → ℝ) => e i (s i)) _ (fun i =>
      HasStrictFDerivAt.comp (0 : Fin m → ℝ) (f := fun s : Fin m → ℝ => s i) (he i).hasStrictFDerivAt
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) i).hasStrictFDerivAt) he0
  have hΨ : HasStrictFDerivAt (fun s => c (pr a (Φ s)))
      ((ContinuousLinearEquiv.refl ℝ (Fin m → ℝ) : (Fin m → ℝ) ≃L[ℝ] (Fin m → ℝ)) : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ)) 0 := by
    have h2 := (c.comp (pr a)).hasStrictFDerivAt.comp 0 hΦd
    refine HasStrictFDerivAt.congr_fderiv h2 (ContinuousLinearMap.ext fun s => ?_)
    have h3 : pr a (∑ i, s i • Y i) = ∑ i, s i • Y i := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, pr_apply, hY, sub_neg_eq_add, ← two_smul ℝ (Y i), smul_smul (1 / 2 : ℝ)]
      norm_num
    have h4 : (∑ i, (ContinuousLinearMap.toSpanSingleton ℝ (Y i)).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) i)) s = ∑ i, s i • Y i := by
      rw [sum_apply]
      rfl
    change c (pr a ((∑ i, (ContinuousLinearMap.toSpanSingleton ℝ (Y i)).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) i)) s)) = s
    rw [h4, h3, hc]
  set ρ := hΨ.localInverse _ _ _ with hρ
  have hz : c (pr a (Φ 0)) = c (pr a (g 0)) := by rw [hΦ0, hg0]
  have hk : HasDerivAt (fun t => c (pr a (g t))) (c (pr a Z)) 0 :=
    (c.comp (pr a)).hasFDerivAt.comp_hasDerivAt 0 hg
  have hρ0 : ρ (c (pr a (g 0))) = 0 := by
    rw [← hz]
    exact hΨ.localInverse_apply_image
  have hρd := hΨ.to_localInverse.hasFDerivAt
  rw [hz] at hρd
  have hs : HasDerivAt (fun t => ρ (c (pr a (g t)))) (c (pr a Z)) 0 := by
    have h5 := hρd.comp_hasDerivAt 0 hk
    exact h5
  refine ⟨fun t => ρ (c (pr a (g t))), hρ0, hs, ?_⟩
  have hr := hΨ.eventually_right_inverse
  rw [hz] at hr
  have near : ∀ k : ℝ → A, ContinuousAt k 0 → k 0 = 1 → ∀ᶠ t in 𝓝 (0 : ℝ), ‖1 - a (k t)‖ ≤ 1 / 2 := fun k hk hk0 => by
    have h4 : ContinuousAt (fun t => ‖1 - a (k t)‖) 0 :=
      (continuousAt_const.sub (a.continuous.continuousAt.comp hk)).norm
    have h5 := h4.tendsto
    simp only [hk0, h1, sub_self, norm_zero] at h5
    exact h5.eventually (eventually_le_nhds (by norm_num))
  have hΦc : ContinuousAt (fun t => Φ (ρ (c (pr a (g t))))) 0 :=
    ContinuousAt.comp_of_eq (g := Φ) (f := fun t => ρ (c (pr a (g t)))) hΦd.continuousAt hs.continuousAt hρ0
  filter_upwards [hk.continuousAt.tendsto hr, near g hg.continuousAt hg0,
    near _ hΦc (by simp only [hρ0, hΦ0])] with t t1 t2 t3
  exact (hgG t).eq_of_pr (hΦG _) t2 t3
    (hc' _ _ ((hgG t).anti ha h1) ((hΦG _).anti ha h1) (Eq.symm t1))

theorem gr_exp [CompleteSpace A] (ha : ∀ x y, a (x * y) = a y * a x) (h1 : a 1 = 1) {Y : A} (hY : a Y = -Y) :
    Gr a (NormedSpace.exp Y) := by
  let _ : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  let φ : A →+* Aᵐᵒᵖ :=
    { toFun := fun x => MulOpposite.op (a x)
      map_one' := by rw [h1]; rfl
      map_mul' := fun x y => by rw [ha]; rfl
      map_zero' := by rw [map_zero]; rfl
      map_add' := fun x y => by rw [map_add (f := _)]; rfl }
  have h2 := NormedSpace.map_exp φ (MulOpposite.continuous_op.comp a.continuous) Y
  have h3 : a (NormedSpace.exp Y) = NormedSpace.exp (-Y) := by
    apply MulOpposite.op_injective
    rw [← hY, ← NormedSpace.exp_op]
    exact h2
  constructor
  · rw [h3, ← NormedSpace.exp_add_of_commute (Commute.refl Y).neg_left, neg_add_cancel, NormedSpace.exp_zero]
  · rw [h3, ← NormedSpace.exp_add_of_commute (Commute.refl Y).neg_right, add_neg_cancel, NormedSpace.exp_zero]

theorem main [FiniteDimensional ℝ A] (ha : ∀ x y, a (x * y) = a y * a x) (h1 : a 1 = 1) :
    ∃ (m : ℕ) (Y : Fin m → A) (c : Fin m → A →ₗ[ℝ] ℝ), (∀ i, a (Y i) = -Y i) ∧ ∀ Z : A,
      (∀ t : ℝ, Gr a (NormedSpace.exp (t • Z))) → ∃ s : Fin m → ℝ → ℝ, (∀ i, s i 0 = 0) ∧ (∀ i, HasDerivAt (s i) (c i Z) 0) ∧
        ∀ᶠ t in 𝓝 (0 : ℝ), NormedSpace.exp (t • Z) = (List.ofFn fun i => NormedSpace.exp (s i t • Y i)).prod := by
  have : CompleteSpace A := FiniteDimensional.complete ℝ A
  let L : Submodule ℝ A := LinearMap.ker ((a : A →ₗ[ℝ] A) + LinearMap.id)
  have hL : ∀ x, x ∈ L ↔ a x = -x := fun x => by
    simp [L, LinearMap.mem_ker, add_eq_zero_iff_eq_neg]
  let b := Module.finBasis ℝ L
  obtain ⟨q, hq⟩ := L.subtype.exists_leftInverse_of_injective L.ker_subtype
  have hq' : ∀ x : L, q x = x := fun x => LinearMap.congr_fun hq x
  let c : A →L[ℝ] (Fin (Module.finrank ℝ L) → ℝ) := LinearMap.toContinuousLinearMap (b.equivFun.toLinearMap ∘ₗ q)
  have hc0 : ∀ x : L, c x = b.equivFun x := fun x => by
    change b.equivFun (q x) = _
    rw [hq']
  refine ⟨_, fun i => b i, fun i => (LinearMap.proj (R := ℝ) (φ := fun _ => ℝ) i).comp (c.comp (pr a)).toLinearMap,
    fun i => (hL _).1 (b i).2, fun Z hZ => ?_⟩
  obtain ⟨s, s0, sd, se⟩ := coords ha h1 (fun i => (b i : A)) (fun i => (hL _).1 (b i).2) c
    (fun s => by
      have : (∑ i, s i • (b i : A)) = ((b.equivFun.symm s : L) : A) := by simp [Module.Basis.equivFun_symm_apply]
      rw [this, hc0, LinearEquiv.apply_symm_apply])
    (fun x y hx hy e => by
      have e1 := (hc0 ⟨x, (hL x).2 hx⟩).symm.trans (e.trans (hc0 ⟨y, (hL y).2 hy⟩))
      exact congrArg Subtype.val (b.equivFun.injective e1))
    (fun i t => NormedSpace.exp (t • (b i : A)))
    (fun i => by simpa using hasStrictDerivAt_exp_smul_const (𝕂 := ℝ) (b i : A) (0 : ℝ))
    (fun i => by simp)
    (fun i t => gr_exp ha h1 (by rw [map_smul, (hL _).1 (b i).2, smul_neg]))
    (fun t => NormedSpace.exp (t • Z)) Z
    (by simpa using hasDerivAt_exp_smul_const (𝕂 := ℝ) Z (0 : ℝ)) (by simp) hZ
  exact ⟨fun i t => s t i, fun i => congrFun s0 i, fun i => hasDerivAt_pi.1 sd i, se⟩

end Alg

end PositivityTheory.ThKEst.LinDerPf

end
end

noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace LinDerPf

section Cx

variable {ι : Type} [Fintype ι] {d : ℕ}

def adj (J : ι → Matrix (Fin d) (Fin d) ℂ) : (ι → Matrix (Fin d) (Fin d) ℂ) →ₗ[ℝ] (ι → Matrix (Fin d) (Fin d) ℂ) where
  toFun x w := ((J w)⁻¹ * (x w)ᵀ * J w).map star
  map_add' x y := by
    funext w
    ext i j
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.transpose_add, Pi.add_apply, Matrix.map_apply, Matrix.add_apply,
      star_add]
  map_smul' r x := by
    funext w
    ext i j
    simp only [Matrix.transpose_smul, Pi.smul_apply, Matrix.mul_smul, Matrix.smul_mul, Matrix.map_apply,
      Matrix.smul_apply, star_smul, RingHom.id_apply, star_trivial]

omit [Fintype ι] in
theorem adj_iff {J : ι → Matrix (Fin d) (Fin d) ℂ} (hJ : ∀ w, IsUnit (J w).det) (Y : ι → Matrix (Fin d) (Fin d) ℂ) :
    adj J Y = -Y ↔ ∀ w, (Y w)ᵀ * J w + J w * (Y w).map star = 0 := by
  rw [funext_iff]
  refine forall_congr' fun w => ?_
  change ((J w)⁻¹ * (Y w)ᵀ * J w).map star = -Y w ↔ _
  have e : ((J w)⁻¹ * (Y w)ᵀ * J w).map star = -Y w ↔ (J w)⁻¹ * (Y w)ᵀ * J w = -(Y w).map star := by
    simp only [← Matrix.ext_iff, Matrix.map_apply, Matrix.neg_apply]
    refine forall_congr' fun i => forall_congr' fun j => ?_
    rw [star_eq_iff_star_eq, star_neg, eq_comm]
  rw [e, add_eq_zero_iff_eq_neg, ← Matrix.mul_neg]
  constructor
  · intro h
    rw [← h, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ (hJ w)]
  · intro h
    rw [Matrix.mul_assoc, h, Matrix.nonsing_inv_mul_cancel_left _ _ (hJ w)]

set_option backward.isDefEq.respectTransparency false in
open scoped Matrix.Norms.Operator in
theorem mainM {J : ι → Matrix (Fin d) (Fin d) ℂ} (hJ : ∀ w, IsUnit (J w).det) :
    ∃ (m : ℕ) (Y : Fin m → ι → Matrix (Fin d) (Fin d) ℂ) (c : Fin m → (ι → Matrix (Fin d) (Fin d) ℂ) →ₗ[ℝ] ℝ),
      (∀ i w, (Y i w)ᵀ * J w + J w * (Y i w).map star = 0) ∧ ∀ Z Z' : ι → Matrix (Fin d) (Fin d) ℂ,
      (∀ w, (Z' w)ᵀ * J w + J w * (Z' w).map star = 0) →
      (∀ w (t : ℝ), NormedSpace.exp ((t : ℂ) • Z w) = NormedSpace.exp ((t : ℂ) • Z' w)) →
      ∃ s : Fin m → ℝ → ℝ, (∀ i, s i 0 = 0) ∧ (∀ i, HasDerivAt (s i) (c i Z) 0) ∧
        ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), ∀ w, NormedSpace.exp ((t : ℂ) • Z w) =
          (List.ofFn fun i => NormedSpace.exp ((s i t : ℂ) • Y i w)).prod := by
  let a : (ι → Matrix (Fin d) (Fin d) ℂ) →L[ℝ] (ι → Matrix (Fin d) (Fin d) ℂ) := LinearMap.toContinuousLinearMap (adj J)
  have ha : ∀ x y, a (x * y) = a y * a x := fun x y => by
    funext w
    change ((J w)⁻¹ * (x w * y w)ᵀ * J w).map (starRingEnd ℂ) =
      ((J w)⁻¹ * (y w)ᵀ * J w).map (starRingEnd ℂ) * ((J w)⁻¹ * (x w)ᵀ * J w).map (starRingEnd ℂ)
    rw [← Matrix.map_mul, Matrix.transpose_mul]
    congr 1
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ (hJ w)]
  have h1 : a 1 = 1 := by
    funext w
    change ((J w)⁻¹ * (1 : Matrix (Fin d) (Fin d) ℂ)ᵀ * J w).map (starRingEnd ℂ) = 1
    rw [Matrix.transpose_one, Matrix.mul_one, Matrix.nonsing_inv_mul _ (hJ w), Matrix.map_one _ (map_zero _) (map_one _)]
  have hx : ∀ (t : ℝ) (x : ι → Matrix (Fin d) (Fin d) ℂ) w,
      NormedSpace.exp (t • x) w = NormedSpace.exp ((t : ℂ) • x w) := fun t x w => by
    rw [Pi.coe_exp, Pi.smul_apply, Complex.coe_smul]
  obtain ⟨m, Y, c, hY, h⟩ := main (a := a) ha h1
  refine ⟨m, Y, c, fun i => (adj_iff hJ _).1 (hY i), fun Z Z' hZ e => ?_⟩
  obtain ⟨s, s0, sd, se⟩ := h Z fun t => by
    have e' : NormedSpace.exp (t • Z) = NormedSpace.exp (t • Z') := funext fun w => by rw [hx, hx, e]
    rw [e']
    refine gr_exp ha h1 ?_
    rw [map_smul, ← smul_neg]
    exact congrArg _ ((adj_iff hJ _).2 hZ)
  refine ⟨s, s0, sd, se.mono fun t ht w => ?_⟩
  rw [← hx, ht, Pi.list_prod_apply, List.map_ofFn]
  congr 2
  funext i
  exact hx _ _ _

end Cx

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {d : ℕ}

omit [NumberField E] in
theorem uat_prod {W : Spc F E d} (l : List (UA σ W.J)) (hl : ∀ g ∈ l, g ∈ UAt σ W (evI F)) :
    l.prod ∈ UAt σ W (evI F) := by
  induction l with
  | nil =>
    intro c _
    change c • ((1 : Matrix (Fin d) (Fin d) (AE F E)) - 1) = 0
    rw [sub_self, smul_zero]
  | cons x l ih =>
    intro c hc
    have h1 := hl x (by simp) c hc
    have h2 := ih (fun g hg => hl g (by simp [hg])) c hc
    rw [List.prod_cons]
    change c • (mat x * mat l.prod - 1) = 0
    have e : mat x * mat l.prod - 1 = mat x * (mat l.prod - 1) + (mat x - 1) := by
      rw [Matrix.mul_sub, Matrix.mul_one, sub_add_sub_cancel]
    rw [e, smul_add, ← Matrix.mul_smul, h1, h2, Matrix.mul_zero, add_zero]

omit [NumberField E] in
theorem mat_prod {J : Matrix (Fin d) (Fin d) E} (p : AE F E →+* ℂ) (l : List (UA σ J)) :
    (mat l.prod).map p = (l.map fun g => (mat g).map p).prod := by
  induction l with
  | nil => exact Matrix.map_one _ (map_zero _) (map_one _)
  | cons x l ih =>
    rw [List.prod_cons, List.map_cons, List.prod_cons, ← ih, ← Matrix.map_mul]
    rfl

theorem uat_ext (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) {W : Spc F E d} {u v : UA σ W.J}
    (hu : u ∈ UAt σ W (evI F)) (hv : v ∈ UAt σ W (evI F))
    (e : ∀ w, (mat u).map (piInf (τ w)) = (mat v).map (piInf (τ w))) : u = v := by
  refine Subtype.ext (Units.ext ?_)
  change mat u = mat v
  ext i j
  refine sub_eq_zero.1 (GlobalTheory.CompanionTheory.CMAdele.eq_zero_of_piInf σ h τ _ (fun c hc => ?_) fun w => ?_)
  · have e1 : c • (mat u - mat v) = 0 := by
      rw [← sub_sub_sub_cancel_right _ _ 1, smul_sub, hu c hc, hv c hc, sub_zero]
    exact congrFun (congrFun e1 i) j
  · rw [map_sub]
    exact sub_eq_zero.2 (congrFun (congrFun (e w) i) j)

end LinDerPf

open LinDerPf in
theorem linDer_of (hG : LineGen) (hX : LineEx) : LinDer := by
  intro F E _ _ _ _ _ σ h τ d W hW
  have hJ : ∀ w, IsUnit (W.J.map (τ w).1).det := fun w => by
    have e : (W.J.map (τ w).1).det = (τ w).1 W.J.det := (RingHom.map_det (τ w).1 W.J).symm
    rw [e]
    exact ((map_ne_zero (τ w).1).2 hW.2).isUnit
  have : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have : IsTopologicalGroup (GL (Fin d) (AE F E)) := inferInstance
  have : IsTopologicalGroup (UA σ W.J) := inferInstance
  obtain ⟨m, Y, c, hY, hm⟩ := mainM hJ
  choose β hβ hβY _ using fun i => hX F E σ h τ d W hW (Y i) (hY i)
  refine ⟨m, β, c, hβ, fun f f' hf γ hγ Z hZ g => ?_⟩
  obtain ⟨Z', hZ', hZZ⟩ := hG F E σ h τ d W hW γ hγ
  obtain ⟨s, s0, sd, se⟩ := hm Z Z' hZ' fun w t => (hZ w t).symm.trans (hZZ w t)
  have h1 := chain f m β (fun i => (hβ i).1) f' (fun i => (hf i).1) (fun i => (hf i).2) (fun _ => g)
    continuousAt_const s (fun i => c i Z) sd s0 0 (hasDerivAt_const _ _)
  rw [zero_add] at h1
  refine h1.congr_of_eventuallyEq (se.mono fun t ht => ?_)
  have e : γ (Multiplicative.ofAdd t) = (List.ofFn fun i => β i (Multiplicative.ofAdd (s i t))).prod := by
    refine uat_ext h τ (hγ.2 _) (uat_prod _ fun x hx => ?_) fun w => ?_
    · obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hx
      exact (hβ i).2 _
    · rw [hZ w t, ht w, mat_prod, List.map_ofFn]
      congr 2
      funext i
      exact (hβY i w _).symm
  simp only [e]

end PositivityTheory.ThKEst

end
end

section -- merged from Development.WeilBound.ThetaLifts.FrameEstimates.OneMemLines
noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section

variable {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W}
  {r s r' s' : ℕ}

theorem exists_clm (hB : ThetaBasic) (hp : IsPair B M χX χW om r s r' s') {𝓕} (hD : Dom M om 𝓕) {φ} (hφ : φ ∈ 𝓕)
    (hsb : φ ∈ SB _) (h : UA σ W.J) :
    ∃ L : SInf F (Fin n × Fin d) →L[ℂ] ℂ, ∀ f : SInf F (Fin n × Fin d), L f = M.I om (pureA F f φ) h := by
  obtain ⟨h1, h2⟩ := dom_facts hB hp hD hφ hsb
  refine ⟨⟨⟨⟨fun f => M.I om (pureA F f φ) h, fun f f' => ?_⟩, fun c f => ?_⟩, h2 h⟩, fun _ => rfl⟩
  · have e : pureA F (f + f' : SInf F _) φ = pureA F f φ + pureA F f' φ := by
      funext x; simp [pureA, add_mul]
    unfold Model.I
    rw [e, ← integral_add ((h1 f).1 h) ((h1 f').1 h)]
    exact integral_congr_ae (Eventually.of_forall fun g => theta_add hp (pureA_mem f hsb) (pureA_mem f' hsb) g h)
  · have e : pureA F (c • f : SInf F _) φ = c • pureA F f φ := by
      funext x; simp [pureA, mul_assoc]
    change M.I om (pureA F (c • f : SInf F _) φ) h = c * M.I om (pureA F f φ) h
    unfold Model.I
    rw [e, ← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun g => theta_smul hp c (pureA_mem f hsb) g h)

theorem one_mem_UAt : (1 : UA σ X.J) ∈ UAt σ X (evI F) := fun u _ => by
  have : mat (1 : UA σ X.J) = 1 := rfl
  rw [this, sub_self, smul_zero]

theorem one_mem_Lines : (1 : Multiplicative ℝ →* UA σ X.J) ∈ Lines σ X := ⟨continuous_const, fun _ => one_mem_UAt⟩

end

theorem iDer_of (hB : ThetaBasic) (hO : PositivityTheory.ThKF.ArchOp) (hL : PositivityTheory.ThKF.ArchLie) (hI : IInv) : IDer := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp 𝓕 hD φ hφ hsb f hf
  obtain ⟨-, i2, i3⟩ := hI F E σ B n d X W M χX χW om r s r' s' hp _ (pureA_mem f hsb)
  refine ⟨fun γ hγ => ?_, fun γ hγ => ?_⟩
  · choose T hT using fun t : ℝ => hO F E σ B n d X W M χX χW om r s r' s' hp 1 one_mem_UAt _ (hγ.2 (Multiplicative.ofAdd t))
    obtain ⟨f₁, hf₁, ha, hd⟩ := hL F E σ B n d X W M χX χW om r s r' s' hp 1 one_mem_Lines γ hγ T (fun t => (hT t).1) f hf
    refine ⟨f₁, hf₁, ha, fun h => ?_⟩
    obtain ⟨L, hLf⟩ := exists_clm hB hp hD hφ hsb h
    have := hd L
    rw [hLf] at this
    convert this using 2 with t
    rw [hLf, ← (hT t).1.1 f φ hsb, i3]
  · choose T hT using fun t : ℝ => hO F E σ B n d X W M χX χW om r s r' s' hp _ (hγ.2 (Multiplicative.ofAdd t)) 1 one_mem_UAt
    obtain ⟨f₁, hf₁, ha, hd⟩ := hL F E σ B n d X W M χX χW om r s r' s' hp γ hγ 1 one_mem_Lines T (fun t => (hT t).1) f hf
    refine ⟨f₁, hf₁, ha, funext fun h => ?_⟩
    obtain ⟨L, hLf⟩ := exists_clm hB hp hD hφ hsb h
    have h1 := hd L
    have h2 : (fun t => L (T t f)) = fun _ => M.I om (pureA F f φ) h := funext fun t => by
      rw [hLf, ← (hT t).1.1 f φ hsb, i2]
    rw [h2] at h1
    rw [← hLf]
    exact h1.unique (hasDerivAt_const _ _)

end PositivityTheory.ThKEst

end
end

section -- merged from Development.WeilBound.ThetaLifts.FrameEstimates.UMGLin
noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

theorem umgLin_pow_le {x C : ℝ} {z : ℂ} (hx : 1 ≤ x) {k m : ℕ} (hk : k ≤ m) (h : ‖z‖ ≤ C * x ^ k) :
    ‖z‖ ≤ |C| * x ^ m :=
  h.trans <| mul_le_mul (le_abs_self C) (pow_le_pow_right₀ hx hk) (pow_nonneg (zero_le_one.trans hx) k) (abs_nonneg C)

theorem umgLin_of : UMGLin := by
  intro F E _ _ _ _ _ σ _ _ d W _ f f' hf hf' a b
  obtain ⟨k, S, hfS, hS⟩ := hf
  obtain ⟨k', S', hfS', hS'⟩ := hf'
  refine ⟨max k k', {g | ∃ f₁ ∈ S, ∃ f₁' ∈ S', g = a • f₁ + b • f₁'}, ⟨f, hfS, f', hfS', rfl⟩, ?_⟩
  rintro _ ⟨g, hg, g', hg', rfl⟩
  obtain ⟨hc, ⟨C, hC⟩, hd⟩ := hS g hg
  obtain ⟨hc', ⟨C', hC'⟩, hd'⟩ := hS' g' hg'
  refine ⟨(hc.const_smul a).add (hc'.const_smul b), ⟨‖a‖ * |C| + ‖b‖ * |C'|, fun h => ?_⟩, fun γ hγ => ?_⟩
  · have hx : (1 : ℝ) ≤ (ht h : ℝ) := by exact_mod_cast one_le_ht h
    have h1 := umgLin_pow_le hx (le_max_left k k') (hC h)
    have h2 := umgLin_pow_le hx (le_max_right k k') (hC' h)
    have h3 : ‖(a • g + b • g') h‖ ≤ ‖a‖ * ‖g h‖ + ‖b‖ * ‖g' h‖ := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul]
    have h4 := mul_le_mul_of_nonneg_left h1 (norm_nonneg a)
    have h5 := mul_le_mul_of_nonneg_left h2 (norm_nonneg b)
    linarith
  · obtain ⟨g₂, hg₂, e⟩ := hd γ hγ
    obtain ⟨g₂', hg₂', e'⟩ := hd' γ hγ
    exact ⟨a • g₂ + b • g₂', ⟨g₂, hg₂, g₂', hg₂', rfl⟩, fun h => ((e h).const_mul a).add ((e' h).const_mul b)⟩

end PositivityTheory.ThKEst

end
end

section -- merged from Development.WeilBound.ThetaLifts.FrameEstimates.UMGSmooth
section -- merged from Development.WeilBound.ThetaLifts.FrameEstimates.UMGSmoothA
noncomputable section

namespace PositivityTheory.ThKEst.UMGS

open Filter Topology Function

theorem hasFDerivAt_of_partials {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (k : ℕ) :
    ∀ (Φ : (Fin k → ℝ) → V) (D : Fin k → (Fin k → ℝ) → V), (∀ i, Continuous (D i)) →
      (∀ i t, HasDerivAt (fun s => Φ (update t i (t i + s))) (D i t) 0) →
      ∀ t, HasFDerivAt Φ (∑ i, (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ).smulRight (D i t)) t := by
  induction k with
  | zero =>
    intro Φ D _ _ t
    simpa using hasFDerivAt_of_subsingleton (𝕜 := ℝ) Φ t
  | succ k ih =>
    intro Φ D hc hd t
    have hcons : Continuous fun v : ℝ × (Fin k → ℝ) => (Fin.cons v.1 v.2 : Fin (k + 1) → ℝ) := by
      refine continuous_pi fun i => ?_
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using continuous_fst
      · simp only [Fin.cons_succ]
        exact (continuous_apply j).comp continuous_snd
    have key := hasStrictFDerivAt_uncurry_coprod (𝕜 := ℝ) (u := (t 0, Fin.tail t))
      (f := fun (s : ℝ) (u : Fin k → ℝ) => Φ (Fin.cons s u))
      (f₁ := fun s u => (ContinuousLinearMap.id ℝ ℝ).smulRight (D 0 (Fin.cons s u)))
      (f₂ := fun s u => ∑ i, (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ).smulRight (D i.succ (Fin.cons s u)))
      (Eventually.of_forall fun v => by
        have h := hd 0 (Fin.cons v.1 v.2)
        simp only [Fin.update_cons_zero, Fin.cons_zero] at h
        have h0 : HasDerivAt (fun s => Φ (Fin.cons (v.1 + s) v.2)) (D 0 (Fin.cons v.1 v.2)) (v.1 - v.1) := by
          simpa using h
        have h1 := h0.comp_sub_const v.1 v.1
        simp only [add_sub_cancel] at h1
        exact h1.hasFDerivAt)
      (Eventually.of_forall fun v => ih (fun u => Φ (Fin.cons v.1 u)) (fun i u => D i.succ (Fin.cons v.1 u))
        (fun i => (hc i.succ).comp (hcons.comp (continuous_const.prodMk continuous_id)))
        (fun i u => by
          have h := hd i.succ (Fin.cons v.1 u)
          simpa only [Fin.cons_update, Fin.cons_succ] using h) v.2)
      (((ContinuousLinearMap.smulRightL ℝ ℝ V (ContinuousLinearMap.id ℝ ℝ)).continuous.comp
        ((hc 0).comp hcons)).continuousAt)
      ((continuous_finsetSum Finset.univ fun i _ =>
        (ContinuousLinearMap.smulRightL ℝ (Fin k → ℝ) V (ContinuousLinearMap.proj i)).continuous.comp
          ((hc i.succ).comp hcons)).continuousAt)
    let e : (Fin (k + 1) → ℝ) →L[ℝ] ℝ × (Fin k → ℝ) :=
      (ContinuousLinearMap.proj 0).prod (ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (Fin.succ i))
    have h2 := HasFDerivAt.comp (f := e) t key.hasFDerivAt e.hasFDerivAt
    have h3 : (↿fun (s : ℝ) (u : Fin k → ℝ) => Φ (Fin.cons s u)) ∘ e = Φ := by
      funext x
      exact congrArg Φ (Fin.cons_self_tail x)
    rw [h3] at h2
    refine h2.congr_fderiv ?_
    ext1 x
    simp [e, HasUncurry.uncurry, Fin.sum_univ_succ, Fin.cons_self_tail]

variable {G : Type} [Group G] [TopologicalSpace G] [ContinuousMul G]
  {A : Type} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] {ι : Type} [Fintype ι]

def pr {k : ℕ} (γ : Fin k → (Multiplicative ℝ →* G)) (t : Fin k → ℝ) : G :=
  (List.ofFn fun i => γ i (Multiplicative.ofAdd (t i))).prod

omit [TopologicalSpace G] [ContinuousMul G] in
theorem pr_succ {k : ℕ} (γ : Fin (k + 1) → (Multiplicative ℝ →* G)) (t : Fin (k + 1) → ℝ) :
    pr γ t = γ 0 (Multiplicative.ofAdd (t 0)) * pr (fun i => γ i.succ) (fun i => t i.succ) := by
  simp [pr, List.ofFn_succ]

omit [TopologicalSpace G] [ContinuousMul G] in
theorem pr_zero (γ : Fin 0 → (Multiplicative ℝ →* G)) (t : Fin 0 → ℝ) : pr γ t = 1 := by
  simp [pr]

def Gn (m : ι → G →* A) (γ : Multiplicative ℝ →* G) (Y : ι → A) : Prop :=
  ∀ w (t : ℝ), m w (γ (Multiplicative.ofAdd t)) = NormedSpace.exp (t • Y w)

theorem continuous_pr (k : ℕ) : ∀ γ : Fin k → (Multiplicative ℝ →* G), (∀ i, Continuous (γ i)) → Continuous (pr γ) := by
  induction k with
  | zero => intro γ _; exact continuous_const.congr fun t => (pr_zero γ t).symm
  | succ k ih =>
    intro γ hγ
    refine Continuous.congr ?_ fun t => (pr_succ γ t).symm
    exact ((hγ 0).comp (continuous_ofAdd.comp (continuous_apply 0))).mul
      ((ih _ fun i => hγ i.succ).comp (continuous_pi fun i => continuous_apply _))

theorem contDiff_exp_smul (Y : A) (n : WithTop ℕ∞) : ContDiff ℝ n fun t : ℝ => NormedSpace.exp (t • Y) := by
  have h : ContDiff ℝ n (NormedSpace.exp : A → A) :=
    contDiff_iff_contDiffAt.2 fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt
  exact h.comp (contDiff_id.smul contDiff_const)

theorem contDiff_tail (k : ℕ) (n : WithTop ℕ∞) : ContDiff ℝ n fun (t : Fin (k + 1) → ℝ) (i : Fin k) => t i.succ :=
  contDiff_pi.2 fun i => contDiff_apply ℝ (fun _ => ℝ) i.succ

omit [TopologicalSpace G] [ContinuousMul G] [Fintype ι] in
theorem contDiff_pr (m : ι → G →* A) (n : WithTop ℕ∞) (w : ι) (k : ℕ) : ∀ γ : Fin k → (Multiplicative ℝ →* G),
    (∀ i, ∃ Y, Gn m (γ i) Y) → ContDiff ℝ n (fun t => m w (pr γ t)) ∧ ContDiff ℝ n (fun t => m w (pr γ t)⁻¹) := by
  induction k with
  | zero => intro γ _; simp only [pr_zero]; exact ⟨contDiff_const, contDiff_const⟩
  | succ k ih =>
    intro γ hγ
    obtain ⟨h1, h2⟩ := ih (fun i => γ i.succ) fun i => hγ i.succ
    obtain ⟨Y, hY⟩ := hγ 0
    simp only [pr_succ, mul_inv_rev, map_mul, ← map_inv, ← ofAdd_neg, hY w]
    exact ⟨((contDiff_exp_smul (Y w) n).comp (contDiff_apply ℝ (fun _ => ℝ) 0)).mul (h1.comp (contDiff_tail k n)),
      (h2.comp (contDiff_tail k n)).mul ((contDiff_exp_smul (Y w) n).comp (contDiff_apply ℝ (fun _ => ℝ) 0).neg)⟩

def cj (x : G) (γ : Multiplicative ℝ →* G) : Multiplicative ℝ →* G := (MulAut.conj x⁻¹).toMonoidHom.comp γ

omit [TopologicalSpace G] [ContinuousMul G] in
theorem cj_apply (x : G) (γ : Multiplicative ℝ →* G) (s : Multiplicative ℝ) : cj x γ s = x⁻¹ * γ s * x := by
  simp [cj]

omit [TopologicalSpace G] [ContinuousMul G] [Fintype ι] in
theorem Gn.cj {m : ι → G →* A} {γ : Multiplicative ℝ →* G} {Y : ι → A} (h : Gn m γ Y) (x : G) :
    Gn m (cj x γ) fun w => m w x⁻¹ * Y w * m w x := by
  intro w t
  let : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  let u : Aˣ := Units.map (m w) (toUnits x⁻¹)
  have h1 : (u : A) = m w x⁻¹ := rfl
  have h2 : ((u⁻¹ : Aˣ) : A) = m w x := by simp [u]
  have := NormedSpace.exp_units_conj u (t • Y w)
  rw [h1, h2] at this
  rw [cj_apply, map_mul, map_mul, h w t, ← this, mul_smul_comm, smul_mul_assoc]

omit [TopologicalSpace G] [ContinuousMul G] in
theorem exists_partial (m : ι → G →* A) (L : Set (Multiplicative ℝ →* G)) (hcj : ∀ γ ∈ L, ∀ x, cj x γ ∈ L)
    (hg : ∀ γ ∈ L, ∃ Y, Gn m γ Y) (n : WithTop ℕ∞) (k : ℕ) : ∀ γ : Fin k → (Multiplicative ℝ →* G), (∀ i, γ i ∈ L) →
    ∀ i, ∃ Z : (Fin k → ℝ) → ι → A, ContDiff ℝ n Z ∧ ∀ t, ∃ γ' ∈ L, Gn m γ' (Z t) ∧
      ∀ s, pr γ (update t i (t i + s)) = pr γ t * γ' (Multiplicative.ofAdd s) := by
  induction k with
  | zero => intro γ _ i; exact i.elim0
  | succ k ih =>
    intro γ hγ i
    refine Fin.cases ?_ (fun j => ?_) i
    · obtain ⟨Y, hY⟩ := hg _ (hγ 0)
      refine ⟨fun t w => m w (pr (fun i => γ i.succ) fun i => t i.succ)⁻¹ * Y w *
        m w (pr (fun i => γ i.succ) fun i => t i.succ), contDiff_pi.2 fun w => ?_, fun t =>
        ⟨_, hcj _ (hγ 0) _, hY.cj _, fun s => ?_⟩⟩
      · obtain ⟨h1, h2⟩ := contDiff_pr m n w k (fun i => γ i.succ) fun i => hg _ (hγ i.succ)
        exact ((h2.comp (contDiff_tail k n)).mul contDiff_const).mul (h1.comp (contDiff_tail k n))
      · simp only [pr_succ, cj_apply, update_self, ne_eq, Fin.succ_ne_zero, not_false_eq_true, update_of_ne,
          ofAdd_add, map_mul]
        group
    · obtain ⟨Z, hZ, h⟩ := ih (fun i => γ i.succ) (fun i => hγ i.succ) j
      refine ⟨fun t => Z fun i => t i.succ, hZ.comp (contDiff_tail k n), fun t => ?_⟩
      obtain ⟨γ', h1, h2, h3⟩ := h fun i => t i.succ
      refine ⟨γ', h1, h2, fun s => ?_⟩
      have e : (fun i : Fin k => update t j.succ (t j.succ + s) i.succ) =
          update (fun i : Fin k => t i.succ) j (t j.succ + s) := by
        funext i
        by_cases hi : i = j
        · subst hi; simp
        · simp [hi]
      rw [pr_succ, pr_succ, e, h3, update_of_ne (Fin.succ_ne_zero j).symm, mul_assoc]

theorem contDiff_comp_pr [FiniteDimensional ℝ A] (m : ι → G →* A) (L : Set (Multiplicative ℝ →* G))
    (hc : ∀ γ ∈ L, Continuous γ) (hcj : ∀ γ ∈ L, ∀ x, cj x γ ∈ L) (hg : ∀ γ ∈ L, ∃ Y, Gn m γ Y)
    {r : ℕ} (β : Fin r → (Multiplicative ℝ →* G)) (c : Fin r → (ι → A) →ₗ[ℝ] ℝ) (hβ : ∀ j, β j ∈ L)
    (hl : ∀ (f : G → ℂ) (f' : Fin r → G → ℂ), (∀ j, Continuous (f' j) ∧
      ∀ h, HasDerivAt (fun t : ℝ => f (h * β j (Multiplicative.ofAdd t))) (f' j h) 0) → ∀ γ ∈ L, ∀ Y, Gn m γ Y →
      ∀ h, HasDerivAt (fun t : ℝ => f (h * γ (Multiplicative.ofAdd t))) (∑ j, (c j Y : ℂ) * f' j h) 0)
    (S : Set (G → ℂ)) (hS : ∀ f ∈ S, Continuous f ∧
      ∀ γ ∈ L, ∃ f₂ ∈ S, ∀ h, HasDerivAt (fun t : ℝ => f (h * γ (Multiplicative.ofAdd t))) (f₂ h) 0)
    {k : ℕ} (γ : Fin k → (Multiplicative ℝ →* G)) (hγ : ∀ i, γ i ∈ L) (g : G) (n : ℕ) :
    ∀ f ∈ S, ContDiff ℝ n fun t => f (g * pr γ t) := by
  induction n with
  | zero =>
    intro f hf
    exact contDiff_zero.2 ((hS f hf).1.comp (continuous_const.mul (continuous_pr k γ fun i => hc _ (hγ i))))
  | succ n ih =>
    intro f hf
    choose f' hf'S hf' using fun j => (hS f hf).2 _ (hβ j)
    choose Z hZ hZ' using exists_partial m L hcj hg n k γ hγ
    have hD : ∀ i, ContDiff ℝ n fun t => ∑ j, (c j (Z i t) : ℂ) * f' j (g * pr γ t) := fun i =>
      ContDiff.sum fun j _ => (Complex.ofRealCLM.contDiff.comp
        ((LinearMap.toContinuousLinearMap (c j)).contDiff.comp (hZ i))).mul (ih _ (hf'S j))
    rw [Nat.cast_succ, contDiff_succ_iff_hasFDerivAt]
    refine ⟨_, ?_, hasFDerivAt_of_partials k _ _ (fun i => (hD i).continuous) fun i t => ?_⟩
    · exact ContDiff.sum fun i _ =>
        (ContinuousLinearMap.smulRightL ℝ (Fin k → ℝ) ℂ (ContinuousLinearMap.proj i)).contDiff.comp (hD i)
    · obtain ⟨γ', h1, h2, h3⟩ := hZ' i t
      simp only [h3, ← mul_assoc]
      exact hl f f' (fun j => ⟨(hS _ (hf'S j)).1, hf' j⟩) γ' h1 _ h2 _

end PositivityTheory.ThKEst.UMGS

end
end

noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def umgComp (τ : ∀ w : InfinitePlace F, EmbOver E w) {d : ℕ} (J : Matrix (Fin d) (Fin d) E) (w : InfinitePlace F) :
    UA σ J →* Matrix (Fin d) (Fin d) ℂ :=
  (piInf (τ w)).mapMatrix.toMonoidHom.comp ((Units.coeHom _).comp (Subgroup.subtype _))

theorem umg_continuousMul {d : ℕ} (J : Matrix (Fin d) (Fin d) E) : ContinuousMul (UA σ J) := by
  have : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have : IsTopologicalGroup (GL (Fin d) (AE F E)) := inferInstance
  exact (Subgroup.instIsTopologicalGroupSubtypeMem _).toContinuousMul

theorem umg_cj_mem {d : ℕ} {W : Spc F E d} {γ : Multiplicative ℝ →* UA σ W.J} (hγ : γ ∈ Lines σ W) (x : UA σ W.J) :
    UMGS.cj x γ ∈ Lines σ W := by
  have := umg_continuousMul (σ := σ) W.J
  refine ⟨((continuous_const.mul hγ.1).mul continuous_const).congr fun s => (UMGS.cj_apply x γ s).symm,
    fun t u hu => ?_⟩
  have h := hγ.2 t u hu
  have hm : ∀ a b : UA σ W.J, mat (a * b) = mat a * mat b := fun _ _ => rfl
  have h1 : mat x⁻¹ * mat x = 1 := by rw [← hm, inv_mul_cancel]; rfl
  have e : mat (UMGS.cj x γ t) - 1 = mat x⁻¹ * (mat (γ t) - 1) * mat x := by
    rw [UMGS.cj_apply, hm, hm, mul_sub, sub_mul, mul_one, h1]
  rw [e, ← Matrix.smul_mul, ← Matrix.mul_smul, h, Matrix.mul_zero, Matrix.zero_mul]

open scoped Matrix.Norms.Operator in
theorem umgSmooth_of (hL : LinDer) (hG : LineGen) : UMGSmooth := by
  intro F E _ _ _ _ _ σ hcm τ d W hW f hf k γ hγ g
  obtain ⟨r, β, c, hβ, hl⟩ := hL F E σ hcm τ d W hW
  obtain ⟨k₀, S, hfS, hS⟩ := hf
  have := umg_continuousMul (σ := σ) W.J
  have hGn : ∀ (δ : Multiplicative ℝ →* UA σ W.J) Y, UMGS.Gn (umgComp τ W.J) δ Y ↔ Gen τ W δ Y := fun δ Y =>
    forall₂_congr fun w t => by rw [Complex.coe_smul]; rfl
  refine contDiff_infty.2 fun n => ?_
  exact UMGS.contDiff_comp_pr (umgComp τ W.J) (Lines σ W) (fun _ h => h.1) (fun _ h x => umg_cj_mem h x)
    (fun δ h => (hG F E σ hcm τ d W hW δ h).imp fun Y hY => (hGn δ Y).2 hY.2) β c hβ
    (fun f f' h δ hδ Y hY => hl f f' h δ hδ Y ((hGn δ Y).1 hY)) S
    (fun f hf => ⟨(hS f hf).1, (hS f hf).2.2⟩) γ hγ g n f hfS

end PositivityTheory.ThKEst

end
end

noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem umgSmooth : UMGSmooth := umgSmooth_of (linDer_of lineGen_of lineEx_of) lineGen_of

theorem cuspRapid (h : GlobalTheory.Published.SiegelSetUnitary) : CuspRapid := cuspRapid_of h umgSmooth

theorem level : Level := level_of coefEq_of fourierInj_of (coefBd_of coefReal_of)

theorem iDer (hB : ThetaBasic) (hO : PositivityTheory.ThKF.ArchOp) (hL : PositivityTheory.ThKF.ArchLie) : IDer := iDer_of hB hO hL (iInv_of hB)

theorem iUMG (hB : ThetaBasic) (hO : PositivityTheory.ThKF.ArchOp) (hL : PositivityTheory.ThKF.ArchLie) : IUMG :=
  iUMG_of hB grpTop_of epsOf_of (iDer hB hO hL) level (iInv_of hB)

theorem sigRapid (h : GlobalTheory.Published.SiegelSetUnitary) (hB : ThetaBasic) (hO : PositivityTheory.ThKF.ArchOp) (hL : PositivityTheory.ThKF.ArchLie) :
    PositivityTheory.ThKEnd.Orth.SigRapid :=
  sigRapid_of hB umgLin_of epsOf_of (iUMG hB hO hL) (iInv_of hB) Sq.triplePair_holds (domWeil_of_U (domWeilU h)) (domSoU h)
    soFin_of (cuspRapid h)

end PositivityTheory.ThKEst

end
