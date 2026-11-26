module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.SingleMulJmComm
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.HasDerivAtRealOfComplex

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Weight
noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem KType.kHighest_w {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) :
    Formalism.REAL.KHighest ε (kunits T) Λ T.w := ⟨fun a => T.w_wt a, fun a b hab he => T.w_hw a b hab he⟩

theorem KType.w_ne_zero {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) : T.w ≠ 0 := by
  intro h
  have h1 := T.w_norm
  rw [h, norm_zero] at h1
  exact zero_ne_one h1

theorem KType.kSpan_eq_top {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) :
    Formalism.REAL.kSpan ε (kunits T) T.w = ⊤ := by
  rcases KType.dτ_irred T (Formalism.REAL.kSpan ε (kunits T) T.w)
    (fun a b hab v hv => Formalism.REAL.compact_span_stable T.w a b hab v hv) with h | h
  · exfalso
    have hw := Formalism.REAL.mem_compact_span_self (ε := ε) (F := kunits T) T.w
    rw [h, Submodule.mem_bot] at hw
    exact (KType.w_ne_zero T) hw
  · exact h

theorem KType.hw_unique {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) {ν : Fin n → ℝ} {v : T.V}
    (hv : v ≠ 0) (h : IsKHWVec ε (kunits T) ν v) : ν = Λ ∧ ∃ c : ℂ, v = c • T.w := by
  have hmem : v ∈ Formalism.REAL.kSpan ε (kunits T) T.w := by rw [KType.kSpan_eq_top T]; trivial
  rcases Formalism.REAL.kHiUniq T.V n ε (kunits T) Λ ν T.w v (KType.kRel T) (KType.kUnit T) (KType.kHighest_w T) hmem h with h0 | h1
  · exact absurd h0 hv
  · exact h1

theorem wtw_eq_sum (w : List (Fin n × Fin n)) :
    ∃ c : Fin n → Fin n → ℕ, (∀ a b, c a b ≠ 0 → (b, a) ∈ w) ∧
      -Formalism.REAL.wordWeightShift w = ∑ a, ∑ b, (c a b : ℝ) • root a b := by
  induction w with
  | nil => exact ⟨fun _ _ => 0, fun a b h => absurd rfl h, by simp [Formalism.REAL.wordWeightShift]⟩
  | cons p w ih =>
    obtain ⟨c, hc, heq⟩ := ih
    refine ⟨fun a b => c a b + if a = p.2 ∧ b = p.1 then 1 else 0, ?_, ?_⟩
    · intro a b hab
      change c a b + (if a = p.2 ∧ b = p.1 then 1 else 0) ≠ 0 at hab
      by_cases h : c a b = 0
      · rw [h, zero_add] at hab
        split_ifs at hab with h2
        · obtain ⟨rfl, rfl⟩ := h2
          simp
        · exact absurd rfl hab
      · exact List.mem_cons_of_mem _ (hc a b h)
    · have hs : ∑ a, ∑ b, (((if a = p.2 ∧ b = p.1 then 1 else 0 : ℕ)) : ℝ) • root a b = root p.2 p.1 := by
        rw [Finset.sum_eq_single p.2, Finset.sum_eq_single p.1]
        · simp
        · intro b _ hb
          simp [hb]
        · intro h
          exact absurd (Finset.mem_univ _) h
        · intro a _ ha
          apply Finset.sum_eq_zero
          intro b _
          simp [ha]
        · intro h
          exact absurd (Finset.mem_univ _) h
      have e : ∀ a b, (((c a b + if a = p.2 ∧ b = p.1 then 1 else 0 : ℕ)) : ℝ) • root a b =
          (c a b : ℝ) • root a b + (((if a = p.2 ∧ b = p.1 then 1 else 0 : ℕ)) : ℝ) • root a b :=
        fun a b => by rw [Nat.cast_add, add_smul]
      simp only [e, Finset.sum_add_distrib, hs, ← heq]
      simp only [Formalism.REAL.wordWeightShift, root]
      abel

theorem KType.weight_le {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) {μ : Fin n → ℝ} {v : T.V}
    (hv : v ≠ 0) (hμ : ∀ a, T.dτ (Matrix.single a a 1) v = ((μ a : ℝ) : ℂ) • v) :
    ∃ c : Fin n → Fin n → ℕ, (∀ a b, c a b ≠ 0 → a < b ∧ ε a = ε b) ∧
      Λ - μ = ∑ a, ∑ b, (c a b : ℝ) • root a b := by
  have hmem : v ∈ Formalism.REAL.lowSpan ε (kunits T) T.w := by
    rw [← Formalism.REAL.compact_span_eq_lowering (KType.kRel T) (KType.kHighest_w T), KType.kSpan_eq_top T]; trivial
  obtain ⟨w, hw, hwμ⟩ : ∃ w : List (Fin n × Fin n), (∀ p ∈ w, ε p.1 = ε p.2 ∧ p.2 < p.1) ∧
      Λ + Formalism.REAL.wordWeightShift w = μ := by
    by_contra hne
    push Not at hne
    apply hv
    have horth : ∀ y ∈ Formalism.REAL.lowSpan ε (kunits T) T.w, inner ℂ v y = 0 := by
      intro y hy
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
      · rintro z ⟨w, hw, rfl⟩
        have hwt := Formalism.REAL.word_action_weight (KType.kRel T) (KType.kHighest_w T).1 w (fun q hq => (hw q hq).1)
        exact Formalism.REAL.kWtOrth T.V n ε (kunits T) μ _ v _ (KType.kUnit T) (fun a => hμ a) hwt
          (fun h => hne w hw h.symm)
      · simp
      · intro x y _ _ hx hy; rw [inner_add_right, hx, hy, add_zero]
      · intro a x _ hx; rw [inner_smul_right, hx, mul_zero]
    exact inner_self_eq_zero.mp (horth v hmem)
  obtain ⟨c, hc, he⟩ := wtw_eq_sum (n := n) w
  refine ⟨c, fun a b hab => ?_, ?_⟩
  · have := hw _ (hc a b hab)
    exact ⟨this.2, this.1.symm⟩
  · rw [← he, ← hwμ]; abel

end ReciprocityTheory.ChartRestriction.DS.HW
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ModelDer
noncomputable section

open Matrix Filter Topology

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

section ExpL
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

lemma mder_exp_cont (X : Matrix (Fin n) (Fin n) ℂ) :
    Continuous (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) :=
  NormedSpace.exp_continuous.comp (Complex.continuous_ofReal.smul continuous_const)

end ExpL

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace


open Classical in
def kcurve (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) : ℝ → KG ε :=
  if h : inK ε X then Classical.choose (exists_curve ε h) else fun _ => 1

lemma kcurve_eq (ε : Fin n → Bool) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) :
    kcurve ε X = onepCurve ε hX := by
  unfold kcurve
  rw [dite_eq_left hX]
  funext t
  apply onep_KG_ext
  rw [Classical.choose_spec (exists_curve ε hX) t, toMK_onepCurve]

lemma continuous_onepCurve (ε : Fin n → Bool) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) :
    Continuous (onepCurve ε hX) := by
  apply continuous_induced_rng.2
  apply (isClosedEmbedding_toM ε).isInducing.continuous_iff.2
  have : ((fun g : UJ ε => toM g) ∘ Subtype.val ∘ onepCurve ε hX) =
      fun t : ℝ => NormedSpace.exp ((t : ℂ) • X) := by
    funext t
    exact toMK_onepCurve ε hX t
  rw [this]
  exact mder_exp_cont X

theorem kcurve_spec (ε : Fin n → Bool) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) :
    Continuous (kcurve ε X) ∧ (∀ t, toMK (kcurve ε X t) = NormedSpace.exp ((t : ℂ) • X)) ∧
      ∀ s t, kcurve ε X (s + t) = kcurve ε X s * kcurve ε X t := by
  rw [kcurve_eq ε hX]
  refine ⟨continuous_onepCurve ε hX, toMK_onepCurve ε hX, ?_⟩
  intro s u
  apply onep_KG_ext
  show toMK (onepCurve ε hX (s + u)) = toMK (onepCurve ε hX s) * toMK (onepCurve ε hX u)
  rw [toMK_onepCurve, toMK_onepCurve, toMK_onepCurve,
    show (((s + u : ℝ) : ℂ) • X) = (s : ℂ) • X + (u : ℂ) • X by push_cast; exact add_smul _ _ _]
  exact Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left _).smul_right _)

theorem curve_eq_kcurve (ε : Fin n → Bool) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (γ : ℝ → KG ε)
    (hγ : ∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) : γ = kcurve ε X := by
  funext t
  apply onep_KG_ext
  rw [hγ, (kcurve_spec ε hX).2.1]

theorem differentiableAt_oneParam {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    (φ : ℝ → (V →L[ℂ] V)) (hc : Continuous φ) (h0 : φ 0 = 1) (hadd : ∀ s t, φ (s + t) = φ s * φ t) :
    DifferentiableAt ℝ φ 0 := by
  have : CompleteSpace V := FiniteDimensional.complete ℂ V
  set Φ : ℝ → (V →L[ℂ] V) := fun x => ∫ s in (0:ℝ)..x, φ s with hΦ
  have hΦd : ∀ x, HasDerivAt Φ (φ x) x := fun x => (hc.integral_hasStrictDerivAt 0 x).hasDerivAt
  have hslope : Tendsto (slope Φ 0) (𝓝[≠] 0) (𝓝 (φ 0)) := hasDerivAt_iff_tendsto_slope.1 (hΦd 0)
  rw [h0] at hslope
  have hev : ∀ᶠ h in 𝓝[≠] (0:ℝ), IsUnit (slope Φ 0 h) := hslope (Units.isOpen.mem_nhds isUnit_one)
  obtain ⟨h, hh, hne⟩ := (hev.and self_mem_nhdsWithin).exists
  have hΦ0 : Φ 0 = 0 := by simp [hΦ]
  rw [slope_def_module, hΦ0, sub_zero, sub_zero] at hh
  obtain ⟨u, hu⟩ := hh
  have key : ∀ t, φ t * Φ h = Φ (t + h) - Φ t := by
    intro t
    have h1 := (ContinuousLinearMap.mul ℝ (V →L[ℂ] V) (φ t)).intervalIntegral_comp_comm
      (hc.intervalIntegrable (μ := MeasureTheory.volume) 0 h)
    simp only [ContinuousLinearMap.mul_apply'] at h1
    rw [hΦ]
    dsimp only
    rw [← h1]
    simp_rw [← hadd]
    rw [intervalIntegral.integral_comp_add_left (fun x => φ x) t, add_zero,
      intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  have hrep : φ = fun t => h⁻¹ • (Φ (t + h) - Φ t) * ((u⁻¹ : (V →L[ℂ] V)ˣ) : V →L[ℂ] V) := by
    funext t
    rw [← key, ← mul_smul_comm, ← hu, Units.mul_inv_cancel_right]
  have hD : Differentiable ℝ Φ := fun x => (hΦd x).differentiableAt
  rw [hrep]
  exact ((((hD.comp (differentiable_id.add_const h)) 0).sub (hD 0)).const_smul h⁻¹).mul_const _

section Op

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

def derOp (ε : Fin n → Bool) (τ : KG ε →* unitary (V →L[ℂ] V)) (X : Matrix (Fin n) (Fin n) ℂ) : V →L[ℂ] V :=
  deriv (fun t : ℝ => ((τ (kcurve ε X t) : unitary (V →L[ℂ] V)) : V →L[ℂ] V)) 0

theorem derOp_hasDeriv [FiniteDimensional ℂ V] (ε : Fin n → Bool) (τ : KG ε →* unitary (V →L[ℂ] V))
    (hcont : Continuous τ) (X : Matrix (Fin n) (Fin n) ℂ) (hX : inK ε X) (γ : ℝ → KG ε)
    (hγ : ∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) :
    HasDerivAt (fun t => ((τ (γ t) : unitary (V →L[ℂ] V)) : V →L[ℂ] V)) (derOp ε τ X) 0 := by
  have hγk := curve_eq_kcurve ε hX γ hγ
  subst hγk
  obtain ⟨hc, -, hmul⟩ := kcurve_spec ε hX
  set φ : ℝ → V →L[ℂ] V := fun t => ((τ (kcurve ε X t) : unitary (V →L[ℂ] V)) : V →L[ℂ] V) with hφ
  have h0k : kcurve ε X 0 = 1 := by
    apply onep_KG_ext
    rw [(kcurve_spec ε hX).2.1]
    show NormedSpace.exp (((0 : ℝ) : ℂ) • X) = (1 : Matrix (Fin n) (Fin n) ℂ)
    simp
  have hφc : Continuous φ := continuous_subtype_val.comp (hcont.comp hc)
  have hφ0 : φ 0 = 1 := by
    simp only [hφ, h0k, map_one]
    rfl
  have hφadd : ∀ s t, φ (s + t) = φ s * φ t := by
    intro s t
    simp only [hφ, hmul, map_mul]
    rfl
  exact (differentiableAt_oneParam φ hφc hφ0 hφadd).hasDerivAt

end Op

def rdc (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) (f : KG ε → ℂ) (x : KG ε) : ℂ :=
  deriv (fun t : ℝ => f (x * kcurve ε (cpart1 ε (bdPart ε Z)) t)) 0 +
    Complex.I * deriv (fun t : ℝ => f (x * kcurve ε (cpart2 ε (bdPart ε Z)) t)) 0

end ReciprocityTheory.ChartRestriction.DS.HW
end
end
