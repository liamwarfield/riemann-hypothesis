module

public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.MvPowerSeriesEvalOfPowMem
public import Formalism.DropLevelBounds.Statement
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LegendreBoundsFactorialMultiIndexCapelli

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FormalDiscPointsValuationIntegers
namespace GlobalTheory.ChF

private theorem exists_pow_mem_span_of_not_isUnit {p : ℕ} [Fact p.Prime] {C : Type} [Field C]
    [CharZero C] {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C]
    (hv : v.Integers O) {x : O} (hx : ¬ IsUnit x) :
    ∃ M : ℕ, x ^ M ∈ Ideal.span {(p : O)} := by
  have h1 : v (algebraMap O C x) < 1 :=
    lt_of_le_of_ne (hv.map_le_one x) fun h => hx (hv.isUnit_of_one' h)
  have hp : (0 : NNReal) < v (algebraMap O C (p : O)) := by
    rw [map_natCast, pos_iff_ne_zero, Valuation.ne_zero_iff]
    exact Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  obtain ⟨M, hM⟩ := NNReal.exists_pow_lt_of_lt_one hp h1
  refine ⟨M, Ideal.mem_span_singleton.2 (hv.dvd_of_le ?_)⟩
  rw [map_pow, map_pow]
  exact hM.le

private theorem not_isUnit_algHom_of_constantCoeff_eq_zero {O : Type} [CommRing O] [Nontrivial O]
    {κ : Type} (Φ : MvPowerSeries κ O →ₐ[O] O) (f : MvPowerSeries κ O)
    (hf : MvPowerSeries.constantCoeff f = 0) : ¬ IsUnit (Φ f) := by
  rintro ⟨u, hu⟩
  have h1 : IsUnit (1 - ((u⁻¹ : Oˣ) : O) • f) := by
    rw [MvPowerSeries.isUnit_iff_constantCoeff, map_sub, map_one, Algebra.smul_def, map_mul, hf,
      mul_zero, sub_zero]
    exact isUnit_one
  have h2 := h1.map Φ
  rw [map_sub, map_one, map_smul, ← hu, smul_eq_mul, Units.inv_mul, sub_self] at h2
  exact not_isUnit_zero h2

theorem formalDisc_points_integers : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (κ : Type) [Finite κ], (∀ c : κ → O, (∀ q, ¬ IsUnit (c q)) → ∃! Φ : MvPowerSeries κ O →ₐ[O] O, ∀ q, Φ (MvPowerSeries.X q) = c q) ∧ (∀ (Φ : MvPowerSeries κ O →ₐ[O] O) (f : MvPowerSeries κ O), MvPowerSeries.constantCoeff f = 0 → ¬ IsUnit (Φ f)) ∧ ∀ (Φ : MvPowerSeries κ O →ₐ[O] O) (n : ℕ), ∃ N : ℕ, ∀ f ∈ ((Ideal.span {(p : O)}).map (MvPowerSeries.C : O →+* MvPowerSeries κ O) ⊔ Ideal.span (Set.range (MvPowerSeries.X : κ → MvPowerSeries κ O))) ^ N, Φ f ∈ Ideal.span {(p : O) ^ n} := by
  intro p _ C _ _ _ v O _ _ hv hp hc κ _
  haveI : Nontrivial O := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hp.out (isUnit_of_subsingleton _)
  refine ⟨fun c hcu => ?_, not_isUnit_algHom_of_constantCoeff_eq_zero, fun Φ n => ?_⟩
  · obtain ⟨hex, huniq⟩ := GlobalTheory.mvPowerSeries_eval_of_pow_mem O (Ideal.span {(p : O)}) κ c
      fun j => exists_pow_mem_span_of_not_isUnit hv (hcu j)
    obtain ⟨Φ, hΦ⟩ := hex hc O
    refine ⟨Φ, hΦ, fun Ψ hΨ => ?_⟩
    have := huniq inferInstance O Ψ.toRingHom Φ.toRingHom
      (fun t => (Ψ.commutes t).trans (Φ.commutes t).symm) hΨ hΦ
    exact AlgHom.ext fun g => DFunLike.congr_fun this g
  · obtain ⟨N, hN⟩ := GlobalTheory.NilpotentEval.exists_pow_sup_span_le (Ideal.span {(p : O)})
      (fun q => Φ (MvPowerSeries.X q)) fun q => exists_pow_mem_span_of_not_isUnit hv
        (not_isUnit_algHom_of_constantCoeff_eq_zero Φ _ (MvPowerSeries.constantCoeff_X q))
    refine ⟨N * n, fun f hf => ?_⟩
    rw [← Ideal.span_singleton_pow]
    refine GlobalTheory.NilpotentEval.pow_mul_le hN n ?_
    have hf' := Ideal.mem_map_of_mem Φ.toRingHom hf
    rw [Ideal.map_pow] at hf'
    refine Ideal.pow_right_mono ?_ _ hf'
    rw [Ideal.map_sup]
    refine sup_le_sup ?_ ?_
    · rw [Ideal.map_map, Ideal.map_le_iff_le_comap]
      intro x hx
      rw [Ideal.mem_comap]
      have : (Φ.toRingHom.comp MvPowerSeries.C) x = x := Φ.commutes x
      rwa [this]
    · rw [Ideal.map_span]
      refine Ideal.span_mono ?_
      rintro _ ⟨_, ⟨q, rfl⟩, rfl⟩
      exact ⟨q, rfl⟩

end GlobalTheory.ChF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.MulFlowValLe
open Formalism.UnitaryBoundIntegral Formalism.IncomingBounds

namespace GlobalTheory.FlowScaling

variable {l d : ℕ} [NeZero d]

lemma isFlow_zero {D : ZMod d → ℝ} (hD : ∀ a, 0 ≤ D a) : IsFlow l d D (fun _ _ => 0) :=
  ⟨fun _ _ => le_rfl, fun s => by simpa using hD s⟩

lemma mul_flowVal_le (hl : 1 ≤ l) {D : ZMod d → ℝ} {x : ZMod d → ℕ → ℝ} (hx : IsFlow l d D x) :
    (l : ℝ) * flowVal d x ≤ ∑ a, D a := by
  have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast hl
  unfold flowVal
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  have h2 := hx.2 a
  have h3 : 0 ≤ ∑ i ∈ oddLevels d, x (a - (i : ZMod d)) i :=
    Finset.sum_nonneg fun i _ => hx.1 _ i
  have h4 : (l : ℝ) * ∑ i ∈ oddLevels d, x a i ≤ ∑ i ∈ oddLevels d, (l : ℝ) ^ i * x a i := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    have hi0 : i ≠ 0 := by
      rintro rfl
      exact absurd (Finset.mem_filter.1 hi).2 (by decide)
    exact mul_le_mul_of_nonneg_right (le_self_pow₀ hl1 hi0) (hx.1 a i)
  linarith

lemma flowVal_le (hl : 1 ≤ l) {D : ZMod d → ℝ} {x : ZMod d → ℕ → ℝ} (hx : IsFlow l d D x) :
    flowVal d x ≤ (∑ a, D a) / l := by
  have hl0 : (0 : ℝ) < l := by exact_mod_cast hl
  rw [le_div_iff₀ hl0, mul_comm]
  exact mul_flowVal_le hl hx

lemma le_maxFlow (hl : 1 ≤ l) {D : ZMod d → ℝ} {x : ZMod d → ℕ → ℝ} (hx : IsFlow l d D x) :
    flowVal d x ≤ maxFlow l d D := by
  refine le_csSup ⟨(∑ a, D a) / l, ?_⟩ ⟨x, hx, rfl⟩
  rintro t ⟨y, hy, rfl⟩
  exact flowVal_le hl hy

lemma maxFlow_le {D : ZMod d → ℝ} (hD : ∀ a, 0 ≤ D a) {B : ℝ}
    (h : ∀ x, IsFlow l d D x → flowVal d x ≤ B) : maxFlow l d D ≤ B := by
  refine csSup_le ⟨_, _, isFlow_zero hD, rfl⟩ ?_
  rintro t ⟨y, hy, rfl⟩
  exact h y hy

lemma maxFlow_le_div (hl : 1 ≤ l) {D : ZMod d → ℝ} (hD : ∀ a, 0 ≤ D a) :
    maxFlow l d D ≤ (∑ a, D a) / l :=
  maxFlow_le hD fun _ hx => flowVal_le hl hx

lemma maxFlow_nonneg (hl : 1 ≤ l) {D : ZMod d → ℝ} (hD : ∀ a, 0 ≤ D a) :
    0 ≤ maxFlow l d D := by
  have := le_maxFlow hl (isFlow_zero (l := l) hD)
  simpa [flowVal] using this

lemma mul_maxFlow_le (hl : 1 ≤ l) {c : ℝ} {D D' : ZMod d → ℝ} (hc : 0 ≤ c) (hD : ∀ a, 0 ≤ D a)
    (h : ∀ a, c * D a ≤ D' a) : c * maxFlow l d D ≤ maxFlow l d D' := by
  rcases hc.eq_or_lt with rfl | hc0
  · rw [zero_mul]
    exact maxFlow_nonneg hl fun a => by simpa using h a
  · rw [← le_div_iff₀' hc0]
    refine maxFlow_le hD fun x hx => ?_
    rw [le_div_iff₀' hc0]
    have hf : IsFlow l d D' (fun a i => c * x a i) := by
      refine ⟨fun s i => mul_nonneg hc (hx.1 s i), fun s => le_trans (le_of_eq ?_)
        ((mul_le_mul_of_nonneg_left (hx.2 s) hc).trans (h s))⟩
      rw [mul_add, Finset.mul_sum, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by ring
    have hv : flowVal d (fun a i => c * x a i) = c * flowVal d x := by
      simp only [flowVal, Finset.mul_sum]
    rw [← hv]
    exact le_maxFlow hl hf

lemma maxFlow_mul (hl : 1 ≤ l) {c : ℝ} {D : ZMod d → ℝ} (hc : 0 ≤ c) (hD : ∀ a, 0 ≤ D a) :
    maxFlow l d (fun a => c * D a) = c * maxFlow l d D := by
  refine le_antisymm ?_ (mul_maxFlow_le hl hc hD fun _ => le_rfl)
  rcases hc.eq_or_lt with rfl | hc0
  · have := maxFlow_le_div (D := fun a => 0 * D a) hl (fun a => by simp)
    simpa using this
  · have := mul_maxFlow_le (c := c⁻¹) (D := fun a => c * D a) (D' := D) hl (inv_nonneg.2 hc)
      (fun a => mul_nonneg hc (hD a)) (fun a => by rw [inv_mul_cancel_left₀ hc0.ne'])
    rwa [inv_mul_le_iff₀ hc0] at this

end GlobalTheory.FlowScaling
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.DropLevelsBasic
open Formalism.UnitaryBoundIntegral Formalism.IncomingBounds

namespace GlobalTheory.BasicFlow

lemma pivot {ι κ : Type} [DecidableEq ι] [Fintype κ] (s : Finset ι)
    (T : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)) (φ : (ι → ℝ) →ₗ[ℝ] ℝ)
    (hT : ∀ v : ι → ℝ, (∀ i, i ∉ s → v i = 0) → (∀ i, 0 ≤ v i) → T v = 0 → v = 0)
    (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i) (hs : ∀ i, i ∉ s → x i = 0)
    (hc : Fintype.card κ < (s.filter fun i => x i ≠ 0).card) :
    ∃ y : ι → ℝ, (∀ i, 0 ≤ y i) ∧ T y = T x ∧ φ x ≤ φ y ∧ (∀ i, x i = 0 → y i = 0) ∧
      (s.filter fun i => y i ≠ 0).card < (s.filter fun i => x i ≠ 0).card := by
  set t := s.filter fun i => x i ≠ 0 with ht
  let E : (t → ℝ) →ₗ[ℝ] (ι → ℝ) :=
    { toFun := fun v i => if h : i ∈ t then v ⟨i, h⟩ else 0
      map_add' := fun v w => by ext i; by_cases h : i ∈ t <;> simp [h]
      map_smul' := fun c v => by ext i; by_cases h : i ∈ t <;> simp [h] }
  have hker : LinearMap.ker (T ∘ₗ E) ≠ ⊥ := by
    apply LinearMap.ker_ne_bot_of_finrank_lt
    simpa using hc
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hw' : T (E w) = 0 := hw
  have hE0 : E w ≠ 0 := by
    intro h
    apply hw0
    ext ⟨i, hi⟩
    have := congrFun h i
    simpa [E, hi] using this
  have hEt : ∀ i, i ∉ t → E w i = 0 := fun i hi => by simp [E, hi]
  obtain ⟨v, hv0, hvt, hvT, hvφ⟩ :
      ∃ v : ι → ℝ, v ≠ 0 ∧ (∀ i, i ∉ t → v i = 0) ∧ T v = 0 ∧ 0 ≤ φ v := by
    rcases le_total 0 (φ (E w)) with h | h
    · exact ⟨E w, hE0, hEt, hw', h⟩
    · refine ⟨-E w, neg_ne_zero.2 hE0, fun i hi => by simp [hEt i hi], by simp [hw'], ?_⟩
      simpa using h
  have hneg : (t.filter fun i => v i < 0).Nonempty := by
    by_contra hn
    apply hv0
    refine hT v (fun i hi => hvt i fun h => hi (Finset.mem_filter.1 h).1) (fun i => ?_) hvT
    by_cases hi : i ∈ t
    · by_contra hlt
      exact hn ⟨i, Finset.mem_filter.2 ⟨hi, not_le.1 hlt⟩⟩
    · exact (hvt i hi).ge
  obtain ⟨j, hj, hmin⟩ := Finset.exists_min_image _ (fun i => x i / (-v i)) hneg
  obtain ⟨hjt, hjv⟩ := Finset.mem_filter.1 hj
  have hc0 : 0 ≤ x j / (-v j) := div_nonneg (hx j) (by linarith)
  have hzero : ∀ i, x i = 0 → (x + (x j / (-v j)) • v) i = 0 := by
    intro i hi
    have : v i = 0 := hvt i fun h => (Finset.mem_filter.1 h).2 hi
    simp [hi, this]
  refine ⟨x + (x j / (-v j)) • v, fun i => ?_, by simp [hvT], ?_, hzero, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hi : v i < 0
    · have hit : i ∈ t := by
        by_contra h
        exact hi.ne (hvt i h)
      have := hmin i (Finset.mem_filter.2 ⟨hit, hi⟩)
      rw [le_div_iff₀ (by linarith)] at this
      linarith
    · have := mul_nonneg hc0 (not_lt.1 hi)
      linarith [hx i]
  · rw [map_add (f := _), map_smul, smul_eq_mul]
    have := mul_nonneg hc0 hvφ
    linarith
  · apply Finset.card_lt_card
    refine ⟨fun i hi => ?_, fun h => ?_⟩
    · obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hi
      exact Finset.mem_filter.2 ⟨h1, fun h => h2 (hzero i h)⟩
    · apply (Finset.mem_filter.1 (h hjt)).2
      have : v j ≠ 0 := hjv.ne
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      field_simp
      ring

lemma basic {ι κ : Type} [DecidableEq ι] [Fintype κ] (s : Finset ι)
    (T : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)) (φ : (ι → ℝ) →ₗ[ℝ] ℝ)
    (hT : ∀ v : ι → ℝ, (∀ i, i ∉ s → v i = 0) → (∀ i, 0 ≤ v i) → T v = 0 → v = 0)
    (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i) (hs : ∀ i, i ∉ s → x i = 0) :
    ∃ y : ι → ℝ, (∀ i, 0 ≤ y i) ∧ T y = T x ∧ φ x ≤ φ y ∧ (∀ i, x i = 0 → y i = 0) ∧
      (s.filter fun i => y i ≠ 0).card ≤ Fintype.card κ := by
  induction' h : (s.filter fun i => x i ≠ 0).card using Nat.strong_induction_on
    with n ih generalizing x
  by_cases hc : (s.filter fun i => x i ≠ 0).card ≤ Fintype.card κ
  · exact ⟨x, hx, rfl, le_rfl, fun _ h => h, hc⟩
  · obtain ⟨y, h1, h2, h3, h4, h5⟩ := pivot s T φ hT x hx hs (not_le.1 hc)
    obtain ⟨z, g1, g2, g3, g4, g5⟩ :=
      ih _ (h ▸ h5) y h1 (fun i hi => h4 i (hs i hi)) rfl
    exact ⟨z, g1, g2.trans h2, h3.trans g3, fun i hi => g4 i (h4 i hi), g5⟩

lemma entry_le (l d : ℕ) [NeZero d] (hl : 2 ≤ l) (W : ZMod d → ℝ) (x : ZMod d → ℕ → ℝ)
    (hx : IsFlow l d W x) (a : ZMod d) (i : ℕ) (hi : i ∈ oddLevels d) : x a i ≤ W a := by
  obtain ⟨h0, h2⟩ := hx
  have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast (by omega : 1 ≤ l)
  have e1 : (l : ℝ) ^ i * x a i ≤ ∑ i ∈ oddLevels d, (l : ℝ) ^ i * x a i :=
    Finset.single_le_sum (f := fun i => (l : ℝ) ^ i * x a i)
      (fun j _ => mul_nonneg (by positivity) (h0 a j)) hi
  have e2 : 0 ≤ ∑ i ∈ oddLevels d, x (a - i) i := Finset.sum_nonneg fun j _ => h0 _ j
  have e3 : x a i ≤ (l : ℝ) ^ i * x a i := le_mul_of_one_le_left (h0 a i) (one_le_pow₀ hl1)
  have := h2 a
  linarith

lemma low_optimum (l d : ℕ) [NeZero d] (hl : 2 ≤ l) (W : ZMod d → ℝ) (hW : 0 ≤ W) (i0 : ℕ) :
    ∃ x : ZMod d → ℕ → ℝ, (IsFlow l d W x ∧ ∀ a i, (i0 ≤ i ∨ i ∉ oddLevels d) → x a i = 0) ∧
      ∀ x' : ZMod d → ℕ → ℝ, IsFlow l d W x' →
        (∀ a i, (i0 ≤ i ∨ i ∉ oddLevels d) → x' a i = 0) → flowVal d x' ≤ flowVal d x := by
  let S : Set (ZMod d → ℕ → ℝ) :=
    {x | IsFlow l d W x ∧ ∀ a i, (i0 ≤ i ∨ i ∉ oddLevels d) → x a i = 0}
  have hclosed : IsClosed S := by
    simp only [S, IsFlow, Set.setOf_and, Set.setOf_forall]
    refine IsClosed.inter (IsClosed.inter ?_ ?_) ?_
    · exact isClosed_iInter fun a => isClosed_iInter fun i =>
        isClosed_le continuous_const (by fun_prop)
    · exact isClosed_iInter fun a => isClosed_le (by fun_prop) continuous_const
    · exact isClosed_iInter fun a => isClosed_iInter fun i => isClosed_iInter fun _ =>
        isClosed_eq (by fun_prop) continuous_const
  have hK : IsCompact (Set.pi Set.univ fun a : ZMod d =>
      Set.pi Set.univ fun _ : ℕ => Set.Icc (0 : ℝ) (W a)) :=
    isCompact_univ_pi fun a => isCompact_univ_pi fun _ => isCompact_Icc
  have hS : IsCompact S := by
    refine hK.of_isClosed_subset hclosed ?_
    rintro x ⟨h0, h1⟩ a - i -
    refine ⟨h0.1 a i, ?_⟩
    by_cases h : i ∈ oddLevels d
    · exact entry_le l d hl W x h0 a i h
    · rw [h1 a i (Or.inr h)]; exact hW a
  have hne : S.Nonempty := ⟨fun _ _ => 0, ⟨fun _ _ => le_rfl, fun a => by simpa using hW a⟩,
    fun _ _ _ => rfl⟩
  obtain ⟨x, hx, hmax⟩ := hS.exists_isMaxOn hne
    (f := fun x => flowVal d x) (Continuous.continuousOn (by unfold flowVal; fun_prop))
  exact ⟨x, hx, fun x' h1 h2 => hmax (a := x') ⟨h1, h2⟩⟩

lemma truncate (l d : ℕ) [NeZero d] (hl : 2 ≤ l) (W : ZMod d → ℝ) (i0 : ℕ)
    (x : ZMod d → ℕ → ℝ) (hx : IsFlow l d W x) :
    ∃ x' : ZMod d → ℕ → ℝ, IsFlow l d W x' ∧
      (∀ a i, (i0 ≤ i ∨ i ∉ oddLevels d) → x' a i = 0) ∧
      flowVal d x ≤ flowVal d x' + (∑ a, W a) / (l : ℝ) ^ i0 := by
  obtain ⟨h0, h2⟩ := hx
  have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast (by omega : 1 ≤ l)
  let y : ZMod d → ℕ → ℝ := fun a i => if i0 ≤ i ∨ i ∉ oddLevels d then 0 else x a i
  have hy : ∀ a i, y a i ≤ x a i := fun a i => by
    simp only [y]; split_ifs
    · exact h0 a i
    · exact le_rfl
  refine ⟨y, ⟨fun a i => ?_, fun a => le_trans (add_le_add ?_ ?_) (h2 a)⟩,
    fun a i h => if_pos h, ?_⟩
  · simp only [y]; split_ifs
    · exact le_rfl
    · exact h0 a i
  · exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hy a i) (by positivity)
  · exact Finset.sum_le_sum fun i _ => hy _ i
  · have hp : (0 : ℝ) < (l : ℝ) ^ i0 := by positivity
    rw [← sub_le_iff_le_add', le_div_iff₀ hp]
    unfold flowVal
    rw [← Finset.sum_sub_distrib, Finset.sum_mul]
    refine Finset.sum_le_sum fun a _ => ?_
    have e2 : 0 ≤ ∑ i ∈ oddLevels d, x (a - i) i := Finset.sum_nonneg fun j _ => h0 _ j
    have e3 : (∑ i ∈ oddLevels d, x a i - ∑ i ∈ oddLevels d, y a i) * (l : ℝ) ^ i0
        ≤ ∑ i ∈ oddLevels d, (l : ℝ) ^ i * x a i := by
      rw [← Finset.sum_sub_distrib, Finset.sum_mul]
      refine Finset.sum_le_sum fun i hi => ?_
      by_cases h : i0 ≤ i
      · have : y a i = 0 := if_pos (Or.inl h)
        rw [this, sub_zero, mul_comm]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hl1 h) (h0 a i)
      · have : y a i = x a i := if_neg (by simp [h, hi])
        rw [this, sub_self, zero_mul]
        exact mul_nonneg (by positivity) (h0 a i)
    have := h2 a
    linarith

theorem dropLevelsBasic : DropLevelsBasic := by
  intro l d _ hl W hW i0
  obtain ⟨x, ⟨hx, hx0⟩, hmax⟩ := low_optimum l d hl W hW i0
  have hm : maxFlow l d W ≤ flowVal d x + (∑ a, W a) / (l : ℝ) ^ i0 := by
    refine csSup_le ⟨_, x, hx, rfl⟩ ?_
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨z', h1, h2, h3⟩ := truncate l d hl W i0 z hz
    linarith [hmax z' h1 h2]
  let T : (ZMod d × ℕ → ℝ) →ₗ[ℝ] (ZMod d → ℝ) :=
    { toFun := fun v s => (∑ i ∈ oddLevels d, (l : ℝ) ^ i * v (s, i)) +
        (∑ i ∈ oddLevels d, v (s - (i : ZMod d), i))
      map_add' := fun v w => by
        ext s; simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]; ring
      map_smul' := fun c v => by
        ext s
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_add, Finset.mul_sum,
          mul_left_comm c] }
  let φ : (ZMod d × ℕ → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun v => ∑ s : ZMod d, ∑ i ∈ oddLevels d, v (s, i)
      map_add' := fun v w => by simp only [Pi.add_apply, Finset.sum_add_distrib]
      map_smul' := fun c v => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum] }
  obtain ⟨y, h1, h2, h3, h4, h5⟩ := basic ((Finset.univ : Finset (ZMod d)) ×ˢ oddLevels d) T φ
    (fun v hv hv0 hT => by
      ext ⟨a, i⟩
      by_cases hi : i ∈ oddLevels d
      · refine le_antisymm ?_ (hv0 _)
        exact entry_le l d hl 0 (fun a i => v (a, i))
          ⟨fun a i => hv0 _, fun s => (congrFun hT s).le⟩ a i hi
      · exact hv _ (by simp [hi]))
    (fun p => x p.1 p.2) (fun p => hx.1 _ _)
    (fun p hp => hx0 _ _ (Or.inr (by simpa using hp)))
  refine ⟨fun a i => y (a, i), ⟨fun a i => h1 _, fun s => ?_⟩,
    fun a i h => h4 (a, i) (hx0 a i h), ?_, ?_⟩
  · exact (congrFun h2 s).le.trans (hx.2 s)
  · simpa [ZMod.card] using h5
  · have : flowVal d x ≤ flowVal d (fun a i => y (a, i)) := h3
    linarith

end GlobalTheory.BasicFlow
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.WeightNonnegExpOfWeightGeInvPrimeSubOne
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.WeightNonnegExpOfWeightGeInvPrimeSubOne
open ReciprocityTheory.PGsh

namespace GlobalTheory.ExpWeight

variable {C : Type} [Field C] (v : AddValuation C (WithTop ℝ))
  {σ : Type} [DecidableEq σ] (ρ : σ → ℝ)

theorem _root_.GlobalTheory.ExpWeight.weight_exp :
  (∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (l : ℕ), l.Prime → v (l : C) = 1 → ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (ρ : σ → ℝ) (h : MvPowerSeries σ C), MvPowerSeries.constantCoeff h = 0 →
    (∀ α, (((1 / (l - 1)) - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ) ≤ v (MvPowerSeries.coeff α (h))) → (∀ α, (((0) - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ) ≤ v (MvPowerSeries.coeff α (PowerSeries.subst (h) (PowerSeries.exp C))))) := by
  intro C _ _ v l hl hvl σ _ _ ρ h h0 hh
  set c : ℝ := 1 / ((l : ℝ) - 1) with hc
  set w : (σ →₀ ℕ) → ℝ := fun α => α.sum (fun j e => ρ j * (e : ℝ)) with hw
  have hwadd : ∀ α β : σ →₀ ℕ, w (α + β) = w α + w β := fun α β => by
    simp only [hw]
    exact Finsupp.sum_add_index' (fun j => by simp) (fun j a b => by push_cast; ring)
  have hsumle : ∀ {ι : Type} (s : Finset ι) (f : ι → C) (r : ℝ),
      (∀ i ∈ s, ((r : ℝ) : WithTop ℝ) ≤ v (f i)) → ((r : ℝ) : WithTop ℝ) ≤ v (∑ i ∈ s, f i) := by
    intro ι s f r hf
    refine Finset.sum_induction f (fun x => ((r : ℝ) : WithTop ℝ) ≤ v x) (fun a b ha hb => ?_) ?_ hf
    · exact le_trans (le_min ha hb) (v.map_add a b)
    · simp
  have hpow : ∀ (d : ℕ) (α : σ →₀ ℕ), (((d : ℝ) * c - w α : ℝ) : WithTop ℝ) ≤ v (MvPowerSeries.coeff α (h ^ d)) := by
    intro d
    induction d with
    | zero =>
      intro α
      rw [pow_zero, MvPowerSeries.coeff_one]
      split_ifs with hα
      · subst hα
        simp [hw]
      · simp
    | succ d ih =>
      intro α
      rw [pow_succ, MvPowerSeries.coeff_mul]
      refine hsumle _ _ _ fun p hp => ?_
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
      rw [v.map_mul]
      have e : ((((d + 1 : ℕ) : ℝ) * c - w α : ℝ) : WithTop ℝ) =
          (((d : ℝ) * c - w p.1 : ℝ) : WithTop ℝ) + ((1 / ((l : ℝ) - 1) - w p.2 : ℝ) : WithTop ℝ) := by
        rw [← WithTop.coe_add, ← hp, hwadd, hc]
        congr 1
        push_cast
        ring
      rw [e]
      exact add_le_add (ih p.1) (hh p.2)
  intro α
  have hsub : PowerSeries.HasSubst h := PowerSeries.HasSubst.of_constantCoeff_zero h0
  rw [PowerSeries.coeff_subst hsub]
  refine finsum_induction (fun x => (((0 : ℝ) - w α : ℝ) : WithTop ℝ) ≤ v x) (by simp)
    (fun a b ha hb => le_trans (le_min ha hb) (v.map_add a b)) fun d => ?_
  simp only [PowerSeries.coeff_exp, smul_eq_mul, v.map_mul]
  have hf : (d.factorial : C) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero d
  have hinv : algebraMap ℚ C (1 / (d.factorial : ℚ)) = ((d.factorial : C))⁻¹ := by simp
  rw [hinv]
  obtain ⟨y, hy⟩ := _root_.ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps.exists_real v (inv_ne_zero hf)
  have hfact := _root_.ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps.natCast_eq_factorization v hl hvl (Nat.factorial_ne_zero d)
  have hprod : v ((d.factorial : C))⁻¹ + v (d.factorial : C) = 0 := by
    rw [← v.map_mul, inv_mul_cancel₀ hf, v.map_one]
  rw [hy, hfact, ← WithTop.coe_add, WithTop.coe_eq_zero] at hprod
  have hle := _root_.GlobalTheory.LegendreBounds.upper l hl d
  have hyr : y = -((d.factorial.factorization l : ℕ) : ℝ) := by linarith
  simp only [Nat.padicValNat_def, ← Nat.factorization_def _ hl] at hle
  have hdc : (d : ℝ) / ((l : ℝ) - 1) = d * c := by rw [hc]; ring
  rw [hy]
  calc (((0 : ℝ) - w α : ℝ) : WithTop ℝ) ≤ ((y + ((d : ℝ) * c - w α) : ℝ) : WithTop ℝ) :=
        WithTop.coe_le_coe.mpr (by linarith)
    _ = ((y : ℝ) : WithTop ℝ) + (((d : ℝ) * c - w α : ℝ) : WithTop ℝ) := WithTop.coe_add _ _
    _ ≤ _ := add_le_add le_rfl (hpow d α)

end GlobalTheory.ExpWeight
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.WeightNonnegExpOfWeightGeInvPrimeSubOneStatement
open ReciprocityTheory.PGsh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weight_nonneg_exp_of_weight_ge_inv_prime_sub_one : (∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (l : ℕ), l.Prime → v (l : C) = 1 → ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (ρ : σ → ℝ) (h : MvPowerSeries σ C), MvPowerSeries.constantCoeff h = 0 →
    (∀ α, (((1 / (l - 1)) - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ) ≤ v (MvPowerSeries.coeff α (h))) → (∀ α, (((0) - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ) ≤ v (MvPowerSeries.coeff α (PowerSeries.subst (h) (PowerSeries.exp C))))) := by
  first | exact @GlobalTheory.ExpWeight.weight_exp | exact GlobalTheory.ExpWeight.weight_exp | (intros; apply GlobalTheory.ExpWeight.weight_exp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.DeterminantPairingQuotientValuationLowerBound
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.DeterminantPairingQuotientValuationLowerBound
open ReciprocityTheory.PGsh

namespace GlobalTheory.DetPairingBound

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps

theorem cayDet_isHomogeneous (n : ℕ) (C : Type) [CommRing C] :
    (cayDet n C).IsHomogeneous n := by
  show (Matrix.mvPolynomialX (Fin n) (Fin n) C).det.IsHomogeneous n
  rw [Matrix.det_apply']
  refine IsHomogeneous.sum _ _ _ fun σ _ => ?_
  rw [← map_intCast (MvPolynomial.C : C →+* MvPolynomial (Fin n × Fin n) C)]
  refine IsHomogeneous.C_mul ?_ _
  have h := IsHomogeneous.prod (Finset.univ : Finset (Fin n))
    (fun i => Matrix.mvPolynomialX (Fin n) (Fin n) C (σ i) i) (fun _ => 1)
    (fun i _ => by simpa [Matrix.mvPolynomialX_apply] using isHomogeneous_X (R := C) ((σ i, i) : Fin n × Fin n))
  simpa using h

theorem coeff_cayDet_pow_nonneg (C : Type) [Field C] (v : AddValuation C (WithTop ℝ))
    (n x : ℕ) (A : Fin n × Fin n →₀ ℕ) : 0 ≤ v (AddMonoidAlgebra.coeff (cayDet n C ^ x) A) := by
  rw [← cayDet_map (R := C), ← map_pow, coeff_map, eq_intCast]
  exact intCast_nonneg v _

theorem sum_eq_of_mem_support (C : Type) [CommRing C] (n x : ℕ) (A : Fin n × Fin n →₀ ℕ)
    (hA : A ∈ (cayDet n C ^ x).support) : ∑ j, A j = n * x := by
  have h := (cayDet_isHomogeneous n C).pow x
  rw [← Finsupp.degree_eq_sum]
  by_contra hne
  exact (mem_support_iff.mp hA) (h.coeff_eq_zero hne)

theorem le_val_div {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {N D : C} {a d r : ℝ}
    (hN : (a : WithTop ℝ) ≤ v N) (hD : v D = d) (h : r ≤ a - d) : (r : WithTop ℝ) ≤ v (N / D) := by
  have hD0 : D ≠ 0 := by
    rintro rfl
    simp at hD
  rcases eq_or_ne N 0 with rfl | hN0
  · simp
  · obtain ⟨b, hb⟩ := exists_real v hN0
    rw [div_eq_coe v hD0 hb hD]
    rw [hb, WithTop.coe_le_coe] at hN
    exact WithTop.coe_le_coe.mpr (by linarith)

theorem main : (∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (l : ℕ), l.Prime → v (l : C) = 1 → ∀ (i n₀ s : ℕ) (Q : MvPolynomial (Fin n₀ × Fin n₀) C), 1 ≤ s → 1 ≤ n₀ →
    (∀ A, (((s : ℝ) / 8 - (n₀ : ℝ) ^ 2 * (Real.logb l (n₀ * s) + 1) : ℝ) : WithTop ℝ) ≤ v (AddMonoidAlgebra.coeff Q A)) →
    (((s : ℝ) / 8 - (n₀ : ℝ) ^ 2 * (3 * Real.logb l n₀ + 2 * Real.logb l s + i + 3) : ℝ) : WithTop ℝ) ≤
      v ((∑ A ∈ (cayDet n₀ C ^ (l ^ i * s)).support, AddMonoidAlgebra.coeff (cayDet n₀ C ^ (l ^ i * s)) A * (A.prod fun _ e => (e.factorial : C)) * AddMonoidAlgebra.coeff (Q) A) / (∑ A ∈ (cayDet n₀ C ^ (l ^ i * s)).support, AddMonoidAlgebra.coeff (cayDet n₀ C ^ (l ^ i * s)) A * (A.prod fun _ e => (e.factorial : C)) * AddMonoidAlgebra.coeff (cayDet n₀ C ^ (l ^ i * s)) A))) := by
  intro C _ _ v l hl hvl i n₀ s Q hs hn₀ hQ
  have hvnat : ∀ m : ℕ, m ≠ 0 → v (m : C) = ((padicValNat l m : ℝ) : WithTop ℝ) := by
    intro m hm
    rw [natCast_eq_factorization v hl hvl hm, Nat.factorization_def m hl, ← Nat.padicValNat_def]
  obtain ⟨-, hL2, hL3⟩ := GlobalTheory.LegendreBounds.legendre_bounds l hl
  have hk0 : l ^ i * s ≠ 0 := Nat.mul_ne_zero (pow_ne_zero _ hl.ne_zero) (by omega)

  have hP := GlobalTheory.DetPowPairing.main C n₀ (l ^ i * s)
  rw [← Nat.cast_prod, ← Nat.cast_prod] at hP
  have hF0 : (∏ c ∈ Finset.range n₀, c.factorial) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun c _ => Nat.factorial_ne_zero c
  have hF1 : (∏ c ∈ Finset.range n₀, (l ^ i * s + c).factorial) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun c _ => Nat.factorial_ne_zero _
  have hF0' : ((∏ c ∈ Finset.range n₀, c.factorial : ℕ) : C) ≠ 0 := Nat.cast_ne_zero.mpr hF0
  have hDen := (eq_div_iff hF0').mpr ((mul_comm _ _).trans hP)
  have hvD := div_eq_coe v hF0' (hvnat _ hF1) (hvnat _ hF0)
  rw [← hDen] at hvD

  obtain ⟨wb, hwb⟩ : ∃ wb : ℝ, wb = (n₀ : ℝ) * ((l : ℝ) ^ i * s) / ((l : ℝ) - 1) -
      (n₀ : ℝ) ^ 2 * (Real.logb l ((n₀ : ℝ) * ((l : ℝ) ^ i * s)) + 1) := ⟨_, rfl⟩
  obtain ⟨qb, hqb⟩ : ∃ qb : ℝ, qb = (s : ℝ) / 8 - (n₀ : ℝ) ^ 2 * (Real.logb l (n₀ * s) + 1) :=
    ⟨_, rfl⟩
  have hnum : ∀ A ∈ (cayDet n₀ C ^ (l ^ i * s)).support, ((wb + qb : ℝ) : WithTop ℝ) ≤
      v (AddMonoidAlgebra.coeff (cayDet n₀ C ^ (l ^ i * s)) A * (A.prod fun _ e => (e.factorial : C)) *
        AddMonoidAlgebra.coeff Q A) := by
    intro A hA
    have hsum := sum_eq_of_mem_support C n₀ (l ^ i * s) A hA
    have hW := hL2 (Fin n₀ × Fin n₀) A
      (by rw [hsum]; exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) hk0))
    rw [hsum] at hW
    simp only [Fintype.card_prod, Fintype.card_fin] at hW
    push_cast at hW
    have hwt : (A.prod fun _ e => (e.factorial : C)) = ((∏ j, (A j).factorial : ℕ) : C) := by
      rw [Finsupp.prod_fintype _ _ (fun _ => by simp), Nat.cast_prod]
    have hne : (∏ j, (A j).factorial) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun j _ => Nat.factorial_ne_zero _
    have h2 : (wb : WithTop ℝ) ≤ ((padicValNat l (∏ j, (A j).factorial) : ℝ) : WithTop ℝ) :=
      WithTop.coe_le_coe.mpr (by rw [hwb, sq]; linarith)
    have h3 : (qb : WithTop ℝ) ≤ v (AddMonoidAlgebra.coeff Q A) := by
      rw [hqb]; exact hQ A
    rw [AddValuation.map_mul, AddValuation.map_mul, hwt, hvnat _ hne]
    calc ((wb + qb : ℝ) : WithTop ℝ) = 0 + (wb : WithTop ℝ) + (qb : WithTop ℝ) := by
          rw [zero_add, WithTop.coe_add]
      _ ≤ _ := add_le_add (add_le_add (coeff_cayDet_pow_nonneg C v n₀ _ A) h2) h3
  refine le_val_div v (a := wb + qb) (AddValuation.map_le_sum v hnum) hvD ?_

  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.one_lt
  have hn1 : (1 : ℝ) ≤ n₀ := by exact_mod_cast hn₀
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hn0 : (n₀ : ℝ) ≠ 0 := (by linarith : (0 : ℝ) < n₀).ne'
  have hs0 : (s : ℝ) ≠ 0 := (by linarith : (0 : ℝ) < s).ne'
  have hli : (l : ℝ) ^ i ≠ 0 := pow_ne_zero _ (by linarith : (0 : ℝ) < l).ne'
  have hLn := Real.logb_nonneg hl1 hn1
  have hLs := Real.logb_nonneg hl1 hs1
  have hlK : Real.logb l ((n₀ : ℝ) * ((l : ℝ) ^ i * s)) =
      Real.logb l n₀ + i + Real.logb l s := by
    rw [Real.logb_mul hn0 (mul_ne_zero hli hs0), Real.logb_mul hli hs0, Real.logb_pow,
      Real.logb_self_eq_one hl1]
    ring
  have hlQ : Real.logb l ((n₀ : ℝ) * s) = Real.logb l n₀ + Real.logb l s :=
    Real.logb_mul hn0 hs0
  have h3 := hL3 n₀ (l ^ i * s)
  push_cast at h3
  have hsq : (n₀ : ℝ) * (Real.logb l n₀ + 1) ≤ (n₀ : ℝ) ^ 2 * (Real.logb l n₀ + 1) :=
    mul_le_mul_of_nonneg_right (by nlinarith) (by linarith)
  rw [hwb, hqb, hlK, hlQ]
  linarith

end GlobalTheory.DetPairingBound
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.DeterminantPairingQuotientValuationLowerBoundStatement
open ReciprocityTheory.PGsh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.determinantPairing_quotient_valuation_lower_bound : (∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (l : ℕ), l.Prime → v (l : C) = 1 → ∀ (i n₀ s : ℕ) (Q : MvPolynomial (Fin n₀ × Fin n₀) C), 1 ≤ s → 1 ≤ n₀ →
    (∀ A, (((s : ℝ) / 8 - (n₀ : ℝ) ^ 2 * (Real.logb l (n₀ * s) + 1) : ℝ) : WithTop ℝ) ≤ v (AddMonoidAlgebra.coeff Q A)) →
    (((s : ℝ) / 8 - (n₀ : ℝ) ^ 2 * (3 * Real.logb l n₀ + 2 * Real.logb l s + i + 3) : ℝ) : WithTop ℝ) ≤
      v ((∑ A ∈ (cayDet n₀ C ^ (l ^ i * s)).support, AddMonoidAlgebra.coeff (cayDet n₀ C ^ (l ^ i * s)) A * (A.prod fun _ e => (e.factorial : C)) * AddMonoidAlgebra.coeff (Q) A) / (∑ A ∈ (cayDet n₀ C ^ (l ^ i * s)).support, AddMonoidAlgebra.coeff (cayDet n₀ C ^ (l ^ i * s)) A * (A.prod fun _ e => (e.factorial : C)) * AddMonoidAlgebra.coeff (cayDet n₀ C ^ (l ^ i * s)) A))) := by
  first | exact @GlobalTheory.DetPairingBound.main | exact GlobalTheory.DetPairingBound.main | (intros; apply GlobalTheory.DetPairingBound.main <;> assumption)
end
end
