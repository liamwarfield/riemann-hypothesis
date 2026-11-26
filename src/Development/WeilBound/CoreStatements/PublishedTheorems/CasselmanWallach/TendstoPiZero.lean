module

public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.SmoothSeminormAndSobolevBounds
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoubleCoverUpqKsetGeneratedByExp

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.TendstoPiZero
noncomputable section

open Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped Topology

namespace PositivityTheory.CW

namespace SlopeLimitConstant

variable {n : ℕ}

theorem const_of_slope {E : Type} [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E] [T2Space E]
    {p : ℕ → Seminorm ℂ E} (hp : WithSeminorms p) (f : ℝ → E)
    (hf : ∀ t, Tendsto (fun h : ℝ => ((h : ℂ)⁻¹) • (f (t + h) - f t)) (𝓝[≠] 0) (𝓝 0)) : f 1 = f 0 := by
  by_contra hne
  obtain ⟨i, hi⟩ := hp.separating_of_T1 (f 1 - f 0) (sub_ne_zero.2 hne)
  set g : ℝ → ℝ := fun t => p i (f t - f 0) with hg
  have hd : ∀ t, HasDerivAt g 0 t := by
    intro t
    rw [hasDerivAt_iff_tendsto_slope_zero]
    have h1 : Tendsto (fun h : ℝ => p i (((h : ℂ)⁻¹) • (f (t + h) - f t))) (𝓝[≠] 0) (𝓝 0) := by
      have := ((hp.continuous_seminorm i).tendsto 0).comp (hf t)
      rw [map_zero] at this
      exact this
    refine squeeze_zero_norm (fun h => ?_) h1
    rw [norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, map_smul_eq_mul, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_inv]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have := abs_sub_map_le_sub (p i) (f (t + h) - f 0) (f t - f 0)
    simpa [hg] using this
  have hc := is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt) (fun t => (hd t).deriv) 1 0
  apply hi
  have : g 1 = 0 := by rw [hc]; simp [hg]
  simpa [hg] using this

theorem tendsto_pi_zero {ε : Fin n → Bool} {E : Type} [AddCommGroup E] [Module ℂ E] [UniformSpace E]
    [IsUniformAddGroup E] {p : ℕ → Seminorm ℂ E} {π dπ : Mx n → (E →L[ℂ] E)} (hπ : IsSmoothModRep ε p π dπ)
    {ι : Type} {l : Filter ι} {v : ι → E} (hv : Tendsto v l (𝓝 0)) {g : ι → Mx n} {g₀ : Mx n}
    (hg : ∀ x, g x ∈ UJset ε) (hg₀ : Tendsto g l (𝓝 g₀)) : Tendsto (fun x => π (g x) (v x)) l (𝓝 0) := by
  rw [hπ.withSeminorms.tendsto_nhds _ 0]
  intro i δ hδ
  obtain ⟨q, N, hq, hb⟩ := hπ.growth i
  have h1 : Tendsto (fun x => (1 + hs (g x)) ^ N * q (v x)) l (𝓝 ((1 + hs g₀) ^ N * 0)) := by
    refine Tendsto.mul ?_ ?_
    · exact ((tendsto_const_nhds.add ((continuous_hs).tendsto g₀ |>.comp hg₀)).pow N)
    · have := (hq.tendsto 0).comp hv
      rw [map_zero] at this
      exact this
  rw [mul_zero] at h1
  filter_upwards [(tendsto_order.1 h1).2 δ hδ] with x hx
  rw [sub_zero]
  exact lt_of_le_of_lt (hb (g x) (hg x) (v x)) hx

theorem Dw_sub {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {σ : Mx n → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ) {l : List (Mx n)} (hl : ∀ X ∈ l, X ∈ lieSet ε) {x y : H}
    (hx : Sm ε σ x) (hy : Sm ε σ y) : Dw σ l (x - y) = Dw σ l x - Dw σ l y := by
  have hy' : Sm ε σ ((-1 : ℂ) • y) := by
    rw [sm_iff] at hy ⊢
    exact Submodule.smul_mem _ _ hy
  rw [sub_eq_add_neg, ← neg_one_smul ℂ y, Dw_add hσ hl hx hy', Dw_smul hσ hl _ hy, neg_one_smul, ← sub_eq_add_neg]

theorem tendsto_rem {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {σ : Mx n → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ) {E : Type} [AddCommGroup E] [Module ℂ E] [UniformSpace E]
    [IsUniformAddGroup E] {p : ℕ → Seminorm ℂ E} (hp : WithSeminorms p) (hSD : SobDiff ε σ) {T : H →ₗ[ℂ] E}
    (hT : SobBdOn ε σ (Sm ε σ) p T) {X : Mx n} (hX : X ∈ lieSet ε) {w : H} (hw : Sm ε σ w) :
    Tendsto (fun h : ℝ => ((h : ℂ)⁻¹) • T (σ (NormedSpace.exp (h • X)) w - w - (h : ℂ) • dRep σ X w))
      (𝓝[≠] 0) (𝓝 0) := by
  have hwX : Sm ε σ (dRep σ X w) := by
    have := hw.word hσ (l := [X]) (by simpa using hX)
    simpa [Dw] using this
  have hsm : ∀ h : ℝ, Sm ε σ (σ (NormedSpace.exp (h • X)) w - w - (h : ℂ) • dRep σ X w) := by
    intro h
    have h1 := hw.translate hσ (exp_mem_UJ hX h)
    rw [sm_iff] at h1 hw hwX ⊢
    exact Submodule.sub_mem _ (Submodule.sub_mem _ h1 hw) (Submodule.smul_mem _ _ hwX)
  rw [hp.tendsto_nhds _ 0]
  intro j δ hδ
  obtain ⟨S, C, hS, hb⟩ := hT j
  have hl : ∀ l ∈ S, Tendsto (fun h : ℝ =>
      ‖((h : ℂ)⁻¹) • Dw σ l (σ (NormedSpace.exp (h • X)) w - w - (h : ℂ) • dRep σ X w)‖) (𝓝[≠] 0) (𝓝 0) := by
    intro l hlS
    have hl' : ∀ Y ∈ l, Y ∈ lieSet ε := hS l hlS
    have hd := hSD l hl' w hw X hX
    rw [hasDerivAt_iff_tendsto_slope_zero] at hd
    have e0 : Dw σ l (σ (NormedSpace.exp ((0 : ℝ) • X)) w) = Dw σ l w := by
      rw [zero_smul, NormedSpace.exp_zero, sigma_one hσ]
    rw [tendsto_iff_norm_sub_tendsto_zero] at hd
    refine hd.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hh' : (h : ℂ) ≠ 0 := by exact_mod_cast hh
    have htr := hw.translate hσ (exp_mem_UJ hX h)
    have hsw : Sm ε σ ((h : ℂ) • dRep σ X w) := by
      rw [sm_iff] at hwX ⊢
      exact Submodule.smul_mem _ _ hwX
    have hdiff : Sm ε σ (σ (NormedSpace.exp (h • X)) w - w) := by
      rw [sm_iff] at htr hw ⊢
      exact Submodule.sub_mem _ htr hw
    rw [Dw_sub hσ hl' hdiff hsw, Dw_sub hσ hl' htr hw, Dw_smul hσ hl' _ hwX, zero_add, e0,
      ← Complex.coe_smul, Complex.ofReal_inv, smul_sub, smul_sub, smul_sub, smul_smul, inv_mul_cancel₀ hh', one_smul]
  have hsum : Tendsto (fun h : ℝ => C * (S.map fun l =>
      ‖((h : ℂ)⁻¹) • Dw σ l (σ (NormedSpace.exp (h • X)) w - w - (h : ℂ) • dRep σ X w)‖).sum) (𝓝[≠] 0) (𝓝 0) := by
    have := (tendsto_list_sum (l := S) hl).const_mul C
    simpa using this
  have hle : ∀ h : ℝ, p j (((h : ℂ)⁻¹) • T (σ (NormedSpace.exp (h • X)) w - w - (h : ℂ) • dRep σ X w) - 0) ≤
      C * (S.map fun l =>
        ‖((h : ℂ)⁻¹) • Dw σ l (σ (NormedSpace.exp (h • X)) w - w - (h : ℂ) • dRep σ X w)‖).sum := by
    intro h
    rw [sub_zero, map_smul_eq_mul]
    calc ‖((h : ℂ)⁻¹)‖ * p j (T (σ (NormedSpace.exp (h • X)) w - w - (h : ℂ) • dRep σ X w))
        ≤ ‖((h : ℂ)⁻¹)‖ * (C * sobNorm σ S (σ (NormedSpace.exp (h • X)) w - w - (h : ℂ) • dRep σ X w)) :=
          mul_le_mul_of_nonneg_left (hb _ (hsm h)) (norm_nonneg _)
      _ = _ := by
          rw [sobNorm, mul_left_comm, ← List.sum_map_mul_left]
          congr 2
          exact List.map_congr_left fun l _ => (norm_smul _ _).symm
  filter_upwards [(tendsto_order.1 hsum).2 δ hδ] with h hh
  exact lt_of_le_of_lt (hle h) hh

theorem tendsto_key {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {σ : Mx n → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ) {E : Type} [AddCommGroup E] [Module ℂ E] [UniformSpace E]
    [IsUniformAddGroup E] {p : ℕ → Seminorm ℂ E} {π dπ : Mx n → (E →L[ℂ] E)} (hπ : IsSmoothModRep ε p π dπ)
    (hSD : SobDiff ε σ) {T : H →ₗ[ℂ] E} (hT : SobBdOn ε σ (Sm ε σ) p T) {X : Mx n} (hX : X ∈ lieSet ε)
    (hc : ∀ w, Sm ε σ w → T (dRep σ X w) = dπ X (T w)) {w : H} (hw : Sm ε σ w) :
    Tendsto (fun h : ℝ => ((h : ℂ)⁻¹) •
      (π (NormedSpace.exp ((-h) • X)) (T (σ (NormedSpace.exp (h • X)) w)) - T w)) (𝓝[≠] 0) (𝓝 0) := by
  set a := T w
  set b := dπ X a
  have hneg : Tendsto (fun h : ℝ => -h) (𝓝[≠] 0) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun x hx => neg_ne_zero.2 hx⟩
    have := ((continuous_neg (G := ℝ)).tendsto 0).mono_left (nhdsWithin_le_nhds (s := {(0 : ℝ)}ᶜ))
    simpa using this
  have hg : Tendsto (fun h : ℝ => NormedSpace.exp ((-h) • X)) (𝓝[≠] 0) (𝓝 1) := by
    have := ((continuous_exp_smul X).tendsto 0).comp (tendsto_nhdsWithin_iff.1 hneg).1
    simpa [Function.comp_def] using this
  have hgU : ∀ h : ℝ, NormedSpace.exp ((-h) • X) ∈ UJset ε := fun h => exp_mem_UJ hX (-h)
  have hgW : Tendsto (fun h : ℝ => NormedSpace.exp ((-h) • X)) (𝓝[≠] 0) (𝓝[UJset ε] 1) :=
    tendsto_nhdsWithin_iff.2 ⟨hg, Eventually.of_forall hgU⟩

  have t1 := tendsto_pi_zero hπ (tendsto_rem hσ hπ.withSeminorms hSD hT hX hw) hgU hg
  have t2 : Tendsto (fun h : ℝ => ((h : ℂ)⁻¹) • (π (NormedSpace.exp ((-h) • X)) a - a)) (𝓝[≠] 0) (𝓝 (-b)) := by
    have := ((hπ.hasDRep X hX a).comp hneg).neg
    refine this.congr' (Eventually.of_forall fun h => ?_)
    simp only [Function.comp_apply, Complex.ofReal_neg, inv_neg, neg_smul, neg_neg]
  have t3 : Tendsto (fun h : ℝ => π (NormedSpace.exp ((-h) • X)) b) (𝓝[≠] 0) (𝓝 b) := by
    have := ((hπ.continuousOn b) 1 (one_mem_UJ ε)).tendsto.comp hgW
    rw [hπ.map_one] at this
    exact this
  have hsum := (t1.add t2).add t3
  rw [zero_add, neg_add_cancel] at hsum
  refine hsum.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh' : (h : ℂ) ≠ 0 := by exact_mod_cast hh
  have hTu : T (σ (NormedSpace.exp (h • X)) w - w - (h : ℂ) • dRep σ X w) =
      T (σ (NormedSpace.exp (h • X)) w) - a - (h : ℂ) • b := by
    rw [map_sub, map_sub, map_smul, hc w hw]
  rw [hTu, (π (NormedSpace.exp ((-h) • X))).map_smul, map_sub, map_sub, (π (NormedSpace.exp ((-h) • X))).map_smul]
  rw [smul_sub, smul_sub, smul_sub, smul_sub, smul_smul, inv_mul_cancel₀ hh', one_smul]
  abel

end SlopeLimitConstant

open SlopeLimitConstant in
theorem d4b : D4 := by
  intro n ε H _ _ _ σ hU hI E _ _ _ _ _ _ p π dπ hπ hSD T hT X hX hc w hw
  set f : ℝ → E := fun t => π (NormedSpace.exp ((-t) • X)) (T (σ (NormedSpace.exp (t • X)) w)) with hf
  have hmulπ : ∀ a ∈ UJset ε, ∀ b ∈ UJset ε, ∀ y, π a (π b y) = π (a * b) y := by
    intro a ha b hb y
    rw [hπ.map_mul a ha b hb]; rfl
  have hslope : ∀ t, Tendsto (fun h : ℝ => ((h : ℂ)⁻¹) • (f (t + h) - f t)) (𝓝[≠] 0) (𝓝 0) := by
    intro t
    have hwt := hw.translate hU (exp_mem_UJ hX t)
    have hk := tendsto_key hU hπ hSD hT hX hc hwt
    have := ((π (NormedSpace.exp ((-t) • X))).continuous.tendsto 0).comp hk
    rw [map_zero] at this
    refine this.congr' (Eventually.of_forall fun h => ?_)
    simp only [Function.comp_apply, hf, map_smul, map_sub]
    congr 2
    · rw [hmulπ _ (exp_mem_UJ hX _) _ (exp_mem_UJ hX _), ← exp_add_smul, ← sigma_mul hU (exp_mem_UJ hX _)
        (exp_mem_UJ hX _), ← exp_add_smul, neg_add, add_comm h t]
  have h10 := const_of_slope hπ.withSeminorms f hslope
  simp only [hf, neg_zero, zero_smul, NormedSpace.exp_zero, sigma_one hU, hπ.map_one] at h10
  have h11 := congrArg (π (NormedSpace.exp ((1 : ℝ) • X))) h10
  rw [hmulπ _ (exp_mem_UJ hX _) _ (exp_mem_UJ hX _), ← exp_add_smul, add_neg_cancel, zero_smul,
    NormedSpace.exp_zero, hπ.map_one, one_smul] at h11
  simpa using h11

end PositivityTheory.CW
end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.KTypesFiniteOfHighestWeight
noncomputable section

open ReciprocityTheory.ChartRestriction.DS (casimirK IsGlRep IsInfUnitary IsKHWVec IsKStableSub adjSign)
open scoped InnerProductSpace

namespace PositivityTheory.CW.HighestWeightKernel

variable {n : ℕ} {ε : Fin n → Bool} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {E : Fin n → Fin n → Module.End ℂ V}

theorem inner_compact (hU : IsInfUnitary ε E) {a b : Fin n} (h : ε a = ε b) (x y : V) :
    ⟪E b a x, y⟫_ℂ = ⟪x, E a b y⟫_ℂ := by
  have := hU b a x y
  simpa [adjSign, h.symm] using this

theorem exists_hull (hL : LocFin ε E) (W : Submodule ℂ V) [FiniteDimensional ℂ W] :
    ∃ Y : Submodule ℂ V, FiniteDimensional ℂ Y ∧ IsKStableSub ε E Y ∧ W ≤ Y := by
  classical
  choose S hSfin hSmem hSk using hL
  let bW := Module.finBasis ℂ W
  let Y : Submodule ℂ V := ⨆ i, S (bW i : V)
  haveI : ∀ i, FiniteDimensional ℂ (S (bW i : V)) := fun i => hSfin _
  refine ⟨Y, Submodule.finite_iSup _, ?_, ?_⟩
  · intro a b hab v hv
    refine Submodule.iSup_induction (fun i => S (bW i : V)) (motive := fun x => E a b x ∈ Y) hv ?_ ?_ ?_
    · intro i x hx
      exact (le_iSup (fun i => S (bW i : V)) i) (hSk _ a b hab x hx)
    · simp
    · intro x y hx hy
      rw [map_add (f := _)]
      exact add_mem hx hy
  · intro w hw
    have hrep := bW.sum_repr ⟨w, hw⟩
    have hw' : w = ∑ i, (bW.repr ⟨w, hw⟩ i) • (bW i : V) := by
      have := congrArg Subtype.val hrep
      simp only [Submodule.coe_sum, Submodule.coe_smul] at this
      exact this.symm
    rw [hw']
    refine Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ ?_)
    exact (le_iSup (fun i => S (bW i : V)) i) (hSmem _)

theorem inner_casimirK (hU : IsInfUnitary ε E) (w : V) :
    ⟪w, casimirK ε E w⟫_ℂ =
      ((∑ a, ∑ b ∈ Finset.univ.filter (fun b => ε b = ε a), ‖E b a w‖ ^ 2 : ℝ) : ℂ) := by
  simp only [ReciprocityTheory.ChartRestriction.DS.casimirK, LinearMap.sum_apply, Module.End.mul_apply, inner_sum]
  push_cast
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b hb => ?_))
  have hba : ε b = ε a := (Finset.mem_filter.1 hb).2
  rw [← inner_compact hU hba.symm, inner_self_eq_norm_sq_to_K]
  first
    | rfl
    | simp
    | norm_cast

theorem mem_ker_iff (μ : ℝ) (x : V) :
    x ∈ LinearMap.ker (casimirK ε E - (μ : ℂ) • (1 : Module.End ℂ V)) ↔ casimirK ε E x = (μ : ℂ) • x := by
  simp [LinearMap.mem_ker, sub_eq_zero]

theorem sq_le_of_khw (hU : IsInfUnitary ε E) {w : V} (hw0 : w ≠ 0) {μ : ℝ} (hwμ : casimirK ε E w = (μ : ℂ) • w)
    {Λ : Fin n → ℝ} (hkw : IsKHWVec ε E Λ w) : (∑ a, Λ a ^ 2) ≤ μ := by
  have h1 := inner_casimirK hU w
  rw [hwμ, inner_smul_right, inner_self_eq_norm_sq_to_K] at h1
  have h2 : μ * ‖w‖ ^ 2 = ∑ a, ∑ b ∈ Finset.univ.filter (fun b => ε b = ε a), ‖E b a w‖ ^ 2 := by
    apply Complex.ofReal_injective
    rw [Complex.ofReal_mul, Complex.ofReal_pow]
    exact h1
  have h3 : ∑ a, Λ a ^ 2 * ‖w‖ ^ 2 ≤ ∑ a, ∑ b ∈ Finset.univ.filter (fun b => ε b = ε a), ‖E b a w‖ ^ 2 := by
    refine Finset.sum_le_sum (fun a _ => ?_)
    have hmem : a ∈ Finset.univ.filter (fun b => ε b = ε a) := by simp
    have hle := Finset.single_le_sum (f := fun b => ‖E b a w‖ ^ 2) (fun b _ => by positivity) hmem
    have hEa : ‖E a a w‖ ^ 2 = Λ a ^ 2 * ‖w‖ ^ 2 := by
      rw [hkw.1 a, norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    linarith
  have hpos : 0 < ‖w‖ ^ 2 := by positivity
  rw [← Finset.sum_mul] at h3
  nlinarith

theorem mem_of_eig (hgl : IsGlRep E) (hU : IsInfUnitary ε E) (hL : LocFin ε E)
    (h3 : ∀ S : Submodule ℂ V, FiniteDimensional ℂ S → IsKStableSub ε E S → S ≠ ⊥ →
      ∃ (w : V) (μ : Fin n → ℝ), w ∈ S ∧ w ≠ 0 ∧ IsKHWVec ε E μ w)
    (hint : ∀ (v : V) (a : Fin n) (x : ℝ), v ≠ 0 → E a a v = (x : ℂ) • v → ∃ z : ℤ, x = z)
    {Y : Submodule ℂ V} (hYk : IsKStableSub ε E Y) {μ : ℝ}
    (hY : ∀ (w : V) (Λ : Fin n → ℤ), IsKHWVec ε E (fun a => ((Λ a : ℤ) : ℝ)) w →
      (∑ a, ((Λ a : ℤ) : ℝ) ^ 2) ≤ μ → w ∈ Y)
    {v : V} (hv : Eig ε E μ v) : v ∈ Y := by
  classical
  have key : ∀ k : ℕ, ∀ Z : Submodule ℂ V, FiniteDimensional ℂ Z → Module.finrank ℂ Z = k →
      IsKStableSub ε E Z → (∀ z ∈ Z, casimirK ε E z = (μ : ℂ) • z) → Z ≤ Y := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro Z hZf hZk hZs hZc
      by_cases hZ0 : Z = ⊥
      · rw [hZ0]
        exact bot_le
      obtain ⟨w, Λ, hwZ, hw0, hkw⟩ := h3 Z hZf hZs hZ0
      have hΛ : ∀ a, ∃ z : ℤ, Λ a = z := fun a => hint w a (Λ a) hw0 (hkw.1 a)
      choose Λz hΛz using hΛ
      have hkw' : IsKHWVec ε E (fun a => ((Λz a : ℤ) : ℝ)) w := by
        have : Λ = fun a => ((Λz a : ℤ) : ℝ) := funext hΛz
        rw [← this]
        exact hkw
      have hsq : (∑ a, ((Λz a : ℤ) : ℝ) ^ 2) ≤ μ := sq_le_of_khw hU hw0 (hZc w hwZ) hkw'
      have hwY : w ∈ Y := hY w Λz hkw' hsq
      let Kw : Submodule ℂ V := sInf {T | w ∈ T ∧ IsKStableSub ε E T}
      have hKwS : IsKStableSub ε E Kw := by
        intro a b hab x hx
        rw [Submodule.mem_sInf] at hx ⊢
        intro T hT
        exact hT.2 a b hab x (hx T hT)
      have hwKw : w ∈ Kw := Submodule.mem_sInf.2 (fun T hT => hT.1)
      have hKwZ : Kw ≤ Z := sInf_le ⟨hwZ, hZs⟩
      have hKwY : Kw ≤ Y := sInf_le ⟨hwY, hYk⟩
      haveI : FiniteDimensional ℂ Kw := Submodule.finiteDimensional_of_le hKwZ
      have hZ'lt : Kwᗮ ⊓ Z < Z := by
        refine lt_of_le_of_ne inf_le_right (fun h => ?_)
        have hwZ' : w ∈ Kwᗮ ⊓ Z := by
          rw [h]
          exact hwZ
        have h0 : ⟪w, w⟫_ℂ = 0 := Submodule.inner_right_of_mem_orthogonal hwKw hwZ'.1
        exact hw0 (inner_self_eq_zero.1 h0)
      haveI : FiniteDimensional ℂ (Kwᗮ ⊓ Z : Submodule ℂ V) :=
        Submodule.finiteDimensional_of_le inf_le_right
      have hZ'k : IsKStableSub ε E (Kwᗮ ⊓ Z) := by
        intro a b hab x hx
        refine ⟨?_, hZs a b hab x hx.2⟩
        show E a b x ∈ Kwᗮ
        rw [Submodule.mem_orthogonal]
        intro u hu
        rw [← inner_compact hU hab]
        exact Submodule.inner_right_of_mem_orthogonal (hKwS b a hab.symm u hu) hx.1
      have hlt : Module.finrank ℂ (Kwᗮ ⊓ Z : Submodule ℂ V) < k :=
        hZk ▸ Submodule.finrank_lt_finrank_of_lt hZ'lt
      have hZ'le : Kwᗮ ⊓ Z ≤ Y :=
        ih _ hlt _ inferInstance rfl hZ'k (fun z hz => hZc z hz.2)
      have hsplit : Kw ⊔ Kwᗮ ⊓ Z = Z :=
        Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection hKwZ
      rw [← hsplit]
      exact sup_le hKwY hZ'le
  obtain ⟨S, hSf, hvS, hSk⟩ := hL v
  haveI : FiniteDimensional ℂ S := hSf
  let Z : Submodule ℂ V := S ⊓ LinearMap.ker (casimirK ε E - (μ : ℂ) • (1 : Module.End ℂ V))
  have hZk : IsKStableSub ε E Z := by
    intro a b hab x hx
    refine ⟨hSk a b hab x hx.1, ?_⟩
    have hx2 := (mem_ker_iff μ x).1 hx.2
    refine (mem_ker_iff μ _).2 ?_
    have hc := ReciprocityTheory.ChartRestriction.DS.casimirK_comm ε hgl a b hab
    have := congrArg (fun U : Module.End ℂ V => U x) hc
    simp only [Module.End.mul_apply] at this
    rw [this, hx2, map_smul]
  exact key _ Z (Submodule.finiteDimensional_of_le inf_le_left) rfl hZk
    (fun z hz => (mem_ker_iff μ z).1 hz.2) ⟨hvS, (mem_ker_iff μ v).2 hv⟩

end PositivityTheory.CW.HighestWeightKernel

namespace PositivityTheory.CW

open PositivityTheory.CW.HighestWeightKernel

theorem k_types_finite_of_highest_weight (h : KStableHighestWeightVector) : KTypesBoundedFinite := by
  classical
  intro n ε V _ _ E hgl hU hL hfinHW hint R
  let F : Set (Fin n → ℤ) := {Λ | (∑ a, ((Λ a : ℤ) : ℝ) ^ 2) ≤ R}
  have hFfin : F.Finite := by
    refine (Set.Finite.pi (t := fun _ => Set.Icc (-⌈R⌉) ⌈R⌉) (fun _ => Set.finite_Icc _ _)).subset ?_
    intro Λ hΛ a _
    have hsq : ((Λ a : ℤ) : ℝ) ^ 2 ≤ R := by
      refine le_trans ?_ hΛ
      exact Finset.single_le_sum (f := fun b => ((Λ b : ℤ) : ℝ) ^ 2) (fun b _ => by positivity)
        (Finset.mem_univ a)
    have h1 : ((Λ a : ℤ) : ℝ) ≤ ((Λ a : ℤ) : ℝ) ^ 2 := by exact_mod_cast Int.le_self_sq (Λ a)
    have h2 : (-(Λ a : ℤ) : ℝ) ≤ ((Λ a : ℤ) : ℝ) ^ 2 := by
      have := Int.le_self_sq (-(Λ a))
      rw [neg_sq] at this
      exact_mod_cast this
    have hc := Int.le_ceil R
    constructor
    · have : (-(⌈R⌉ : ℤ) : ℝ) ≤ ((Λ a : ℤ) : ℝ) := by linarith
      exact_mod_cast this
    · have : ((Λ a : ℤ) : ℝ) ≤ ((⌈R⌉ : ℤ) : ℝ) := by linarith
      exact_mod_cast this
  haveI : Finite F := hFfin.to_subtype
  let W0 : Submodule ℂ V :=
    ⨆ Λ : F, Submodule.span ℂ {w | IsKHWVec ε E (fun a => ((Λ.1 a : ℤ) : ℝ)) w}
  haveI : ∀ Λ : F, FiniteDimensional ℂ
      (Submodule.span ℂ {w | IsKHWVec ε E (fun a => ((Λ.1 a : ℤ) : ℝ)) w}) := fun Λ => hfinHW _
  haveI : FiniteDimensional ℂ W0 := Submodule.finite_iSup _
  obtain ⟨Y, hYf, hYk, hWY⟩ := exists_hull hL W0
  haveI : FiniteDimensional ℂ Y := hYf
  refine Submodule.finiteDimensional_of_le (S₂ := Y) ?_
  refine Submodule.span_le.2 ?_
  rintro v ⟨μ, hμR, hv⟩
  refine mem_of_eig hgl hU hL (h n ε V E hgl hU) hint hYk (μ := μ) ?_ hv
  intro w Λ hkw hsq
  have hΛF : Λ ∈ F := le_trans hsq hμR
  exact hWY ((le_iSup (fun Λ : F => Submodule.span ℂ
    {w | IsKHWVec ε E (fun a => ((Λ.1 a : ℤ) : ℝ)) w}) ⟨Λ, hΛF⟩) (Submodule.subset_span hkw))

end PositivityTheory.CW

end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.ZetaClassicalZeroFreeRegion
section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.ExistsNormingFunctional
noncomputable section

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum

namespace PositivityTheory.CW

namespace ZeroOnDense

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Mx n → (H →L[ℂ] H)} {E : Type} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [T2Space E]
  {p : ℕ → Seminorm ℂ E}

theorem zero_on (hp : WithSeminorms p) (hD : Dens ε σ) (Φ : H → E)
    (hsub : ∀ x y, Sm ε σ x → Sm ε σ y → Φ (x - y) = Φ x - Φ y)
    (hb : ∀ i, ∃ (S : List (List (Mx n))) (C : ℝ), Words (lieSet ε) S ∧
      ∀ u, Sm ε σ u → p i (Φ u) ≤ C * sobNorm σ S u)
    (h0 : ∀ v, IsKFin ε σ v → Φ v = 0) : ∀ w, Sm ε σ w → Φ w = 0 := by
  intro w hw
  by_contra hne
  obtain ⟨i, hi⟩ := hp.separating_of_T1 _ hne
  obtain ⟨S, C, hS, hC⟩ := hb i
  have key : ∀ δ : ℝ, 0 < δ → p i (Φ w) ≤ |C| * δ := by
    intro δ hδ
    obtain ⟨v, hv, hd⟩ := hD.2.2 w hw S hS δ hδ
    have hvs : Sm ε σ v := hD.1 v hv
    have hwv : Sm ε σ (w - v) := sm_iff.2 ((smooth (Jm ε) σ).sub_mem (sm_iff.1 hw) (sm_iff.1 hvs))
    have e : Φ w = Φ (w - v) := by rw [hsub w v hw hvs, h0 v hv, sub_zero]
    rw [e]
    calc p i (Φ (w - v)) ≤ C * sobNorm σ S (w - v) := hC _ hwv
      _ ≤ |C| * sobNorm σ S (w - v) := mul_le_mul_of_nonneg_right (le_abs_self C) (sobNorm_nonneg _ _ _)
      _ ≤ |C| * δ := mul_le_mul_of_nonneg_left hd.le (abs_nonneg C)
  have hpos : 0 < p i (Φ w) := lt_of_le_of_ne (apply_nonneg _ _) (Ne.symm hi)
  set x := p i (Φ w) with hx
  have h1 := key (x / (2 * (|C| + 1))) (by positivity)
  have h2 : |C| * (x / (2 * (|C| + 1))) < x := by
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith [abs_nonneg C]
  linarith

end ZeroOnDense

theorem d0 : D0 := by
  intro n ε H _ _ _ σ hU hI E _ _ _ _ _ _ p π dπ hπ hD T hT h0
  exact ZeroOnDense.zero_on hπ.withSeminorms hD T (fun x y _ _ => map_sub T x y) hT h0

end PositivityTheory.CW

end
end

noncomputable section

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum

namespace PositivityTheory.CW

private theorem sobNorm_append' {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mx n → H →L[ℂ] H) (S A : List (List (Mx n))) (w : H) :
    sobNorm σ (S ++ A) w = sobNorm σ S w + sobNorm σ A w := by
  simp [sobNorm, List.map_append, List.sum_append]

private theorem sobNorm_nonneg' {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mx n → H →L[ℂ] H) (S : List (List (Mx n))) (w : H) : 0 ≤ sobNorm σ S w := by
  apply List.sum_nonneg
  intro x hx
  obtain ⟨l, -, rfl⟩ := List.mem_map.1 hx
  exact norm_nonneg _

private theorem exists_sobNorm_bound_of_sobBdOn_continuous_seminorm {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {E : Type} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (σ : Mx n → H →L[ℂ] H) (p : ℕ → Seminorm ℂ E) (hp : WithSeminorms p) (T : H →ₗ[ℂ] E)
    (hT : SobBdOn ε σ (Sm ε σ) p T) (q : Seminorm ℂ E) (hq : Continuous q) :
    ∃ (S : List (List (Mx n))) (C : ℝ), Words (lieSet ε) S ∧ 0 ≤ C ∧
      ∀ w, Sm ε σ w → q (T w) ≤ C * sobNorm σ S w := by
  have key : ∀ s : Finset ℕ, ∃ (S : List (List (Mx n))) (C : ℝ), Words (lieSet ε) S ∧ 0 ≤ C ∧
      ∀ w, Sm ε σ w → ∑ j ∈ s, p j (T w) ≤ C * sobNorm σ S w := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨[], 0, fun l hl => by simp at hl, le_rfl, fun w _ => by simp⟩
    | insert j s hj ih =>
      obtain ⟨S, C, hS, hC, hb⟩ := ih
      obtain ⟨S₁, C₁, hS₁, hb₁⟩ := hT j
      refine ⟨S₁ ++ S, max C₁ 0 + C, ?_, by positivity, ?_⟩
      · intro l hl
        rcases List.mem_append.1 hl with h | h
        · exact hS₁ l h
        · exact hS l h
      · intro w hw
        rw [Finset.sum_insert hj, sobNorm_append']
        have h1 := hb₁ w hw
        have h2 := hb w hw
        have n1 := sobNorm_nonneg' σ S₁ w
        have n2 := sobNorm_nonneg' σ S w
        have h3 : C₁ * sobNorm σ S₁ w ≤ max C₁ 0 * sobNorm σ S₁ w :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) n1
        nlinarith [mul_nonneg (le_max_right C₁ 0) n2, mul_nonneg hC n1]
  obtain ⟨s, C0, -, hle⟩ := Seminorm.bound_of_continuous hp q hq
  obtain ⟨S, C, hS, hC, hb⟩ := key s
  refine ⟨S, C0 * C, hS, mul_nonneg C0.2 hC, fun w hw => ?_⟩
  have hsup : (s.sup p) (T w) ≤ ∑ j ∈ s, p j (T w) :=
    Seminorm.finset_sup_apply_le (Finset.sum_nonneg fun _ _ => apply_nonneg _ _)
      (fun i hi => Finset.single_le_sum (f := fun j => p j (T w)) (fun _ _ => apply_nonneg _ _) hi)
  calc q (T w) ≤ (C0 • s.sup p) (T w) := Seminorm.le_def.1 hle (T w)
    _ = (C0 : ℝ) * (s.sup p) (T w) := by rw [Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul]
    _ ≤ (C0 : ℝ) * ∑ j ∈ s, p j (T w) := mul_le_mul_of_nonneg_left hsup C0.2
    _ ≤ (C0 : ℝ) * (C * sobNorm σ S w) := mul_le_mul_of_nonneg_left (hb w hw) C0.2
    _ = C0 * C * sobNorm σ S w := by ring

theorem d3 : D3 := by
  intro hD0 n ε H _ _ _ σ hU hI E _ _ _ _ _ _ p π dπ hπ hDens T hT hSob w hw
  have hJJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
    rw [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> norm_num
  have hJu : IsUnit (Formalism.REAL.Jm ε) := ⟨⟨Formalism.REAL.Jm ε, Formalism.REAL.Jm ε, hJJ, hJJ⟩, rfl⟩
  have hU' : IsURepOn (Formalism.QuantumDeterminants.UH (Formalism.REAL.Jm ε)) σ := hU
  have hp := hπ.withSeminorms
  constructor
  · intro k hk
    have hkU : k ∈ Formalism.QuantumDeterminants.UH (Formalism.REAL.Jm ε) := by
      show kᴴ * Formalism.REAL.Jm ε * k = Formalism.REAL.Jm ε
      have h1 : star k * k = 1 := Matrix.mem_unitaryGroup_iff'.1 hk.1
      rw [mul_assoc, ← hk.2, ← mul_assoc, ← Matrix.star_eq_conjTranspose, h1, one_mul]
    have hkUJ : k ∈ UJset ε := hkU
    let T' : H →ₗ[ℂ] E := T ∘ₗ (σ k).toLinearMap - (π k).toLinearMap ∘ₗ T
    have hT' : ∀ v, T' v = T (σ k v) - π k (T v) := fun _ => rfl
    have hsob : SobBdOn ε σ (Sm ε σ) p T' := by
      intro i
      obtain ⟨S₁, C₁, hS₁, hb₁⟩ := hSob i
      obtain ⟨S₂, C₂, hS₂, hC₂, hb₂⟩ := exists_sobNorm_bound_of_sobBdOn_continuous_seminorm σ p hp T hSob ((p i).comp (π k).toLinearMap)
        ((hp.continuous_seminorm i).comp (π k).continuous)
      refine ⟨S₁.map (List.map fun X => k⁻¹ * X * k) ++ S₂, max C₁ 0 + C₂, ?_, ?_⟩
      · intro l hl
        rcases List.mem_append.1 hl with h | h
        · obtain ⟨l', hl', rfl⟩ := List.mem_map.1 h
          intro Y hY
          obtain ⟨X, hX, rfl⟩ := List.mem_map.1 hY
          exact conj_mem_lie hJu hkU (hS₁ l' hl' X hX)
        · exact hS₂ l h
      · intro v hv
        have hsv : σ k v ∈ smooth (Formalism.REAL.Jm ε) σ := translate_mem hJu hU' hkU hv
        have heq : sobNorm σ S₁ (σ k v) =
            sobNorm σ (S₁.map (List.map fun X => k⁻¹ * X * k)) v := by
          unfold sobNorm
          rw [List.map_map]
          congr 1
          apply List.map_congr_left
          intro l hl
          simp only [Function.comp_apply]
          rw [word_translate hJu hU' hkU hv l (fun X hX => hS₁ l hl X hX), hU.2.1 k hkUJ,
            List.foldr_map]
        have h1 := hb₁ (σ k v) hsv
        have h2 := hb₂ v hv
        have n1 := sobNorm_nonneg' σ (S₁.map (List.map fun X => k⁻¹ * X * k)) v
        have n2 := sobNorm_nonneg' σ S₂ v
        rw [heq] at h1
        rw [hT', sobNorm_append']
        have h3 : (p i) (T (σ k v) - π k (T v)) ≤ p i (T (σ k v)) + p i (π k (T v)) :=
          map_sub_le_add _ _ _
        have h4 : ((p i).comp (π k).toLinearMap) (T v) = p i (π k (T v)) := rfl
        rw [h4] at h2
        have h5 : C₁ * sobNorm σ (S₁.map (List.map fun X => k⁻¹ * X * k)) v ≤
            max C₁ 0 * sobNorm σ (S₁.map (List.map fun X => k⁻¹ * X * k)) v :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) n1
        nlinarith [mul_nonneg (le_max_right C₁ 0) n2, mul_nonneg hC₂ n1]
    have h0 := hD0 n ε H σ hU hI E p π dπ hπ hDens T' hsob
      (fun v hv => by rw [hT', hT.1 k hk v hv, sub_self]) w hw
    rw [hT'] at h0
    exact sub_eq_zero.1 h0
  · intro X hX
    obtain ⟨L, hL⟩ := exists_word hJu hU' [X] (fun Y hY => by
      rw [List.mem_singleton] at hY
      rw [hY]
      exact hX)
    let f : smooth (Formalism.REAL.Jm ε) σ →ₗ[ℂ] E :=
      T ∘ₗ (smooth (Formalism.REAL.Jm ε) σ).subtype ∘ₗ L -
        (dπ X).toLinearMap ∘ₗ T ∘ₗ (smooth (Formalism.REAL.Jm ε) σ).subtype
    obtain ⟨g, hg⟩ := LinearMap.exists_extend f
    have hgw : ∀ v (hv : Sm ε σ v), g v = T (dRep σ X v) - dπ X (T v) := by
      intro v hv
      have h := LinearMap.congr_fun hg ⟨v, hv⟩
      simp only [LinearMap.comp_apply, Submodule.subtype_apply] at h
      rw [h]
      simp only [f, LinearMap.sub_apply, LinearMap.comp_apply, Submodule.subtype_apply, hL,
        List.foldr_cons, List.foldr_nil, ContinuousLinearMap.coe_coe]
    have hsob : SobBdOn ε σ (Sm ε σ) p g := by
      intro i
      obtain ⟨S₁, C₁, hS₁, hb₁⟩ := hSob i
      obtain ⟨S₂, C₂, hS₂, hC₂, hb₂⟩ := exists_sobNorm_bound_of_sobBdOn_continuous_seminorm σ p hp T hSob ((p i).comp (dπ X).toLinearMap)
        ((hp.continuous_seminorm i).comp (dπ X).continuous)
      refine ⟨S₁.map (fun l => l ++ [X]) ++ S₂, max C₁ 0 + C₂, ?_, ?_⟩
      · intro l hl
        rcases List.mem_append.1 hl with h | h
        · obtain ⟨l', hl', rfl⟩ := List.mem_map.1 h
          intro Y hY
          rcases List.mem_append.1 hY with h' | h'
          · exact hS₁ l' hl' Y h'
          · rw [List.mem_singleton.1 h']
            exact hX
        · exact hS₂ l h
      · intro v hv
        have hdv : Sm ε σ (dRep σ X v) := dRep_mem hJu hU' hv hX
        have heq : sobNorm σ S₁ (dRep σ X v) = sobNorm σ (S₁.map (fun l => l ++ [X])) v := by
          unfold sobNorm
          rw [List.map_map]
          congr 1
          apply List.map_congr_left
          intro l _
          simp [List.foldr_append]
        have h1 := hb₁ (dRep σ X v) hdv
        have h2 := hb₂ v hv
        have n1 := sobNorm_nonneg' σ (S₁.map (fun l => l ++ [X])) v
        have n2 := sobNorm_nonneg' σ S₂ v
        rw [heq] at h1
        rw [hgw v hv, sobNorm_append']
        have h3 : (p i) (T (dRep σ X v) - dπ X (T v)) ≤ p i (T (dRep σ X v)) + p i (dπ X (T v)) :=
          map_sub_le_add _ _ _
        have h4 : ((p i).comp (dπ X).toLinearMap) (T v) = p i (dπ X (T v)) := rfl
        rw [h4] at h2
        have h5 : C₁ * sobNorm σ (S₁.map (fun l => l ++ [X])) v ≤
            max C₁ 0 * sobNorm σ (S₁.map (fun l => l ++ [X])) v :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) n1
        nlinarith [mul_nonneg (le_max_right C₁ 0) n2, mul_nonneg hC₂ n1]
    have h0 := hD0 n ε H σ hU hI E p π dπ hπ hDens g hsob
      (fun v hv => by rw [hgw v (hDens.1 v hv), hT.2 X hX v hv, sub_self]) w hw
    rw [hgw w hw] at h0
    exact sub_eq_zero.1 h0

end PositivityTheory.CW

end
end
