module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.UpDivStatementPfE

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.UpDivStatementPfF
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.UpDivStatementPfC
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.UpDivStatementPfB
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.UpDivStatementPfA
namespace ReciprocityTheory.ChartRestriction.G.AR.Up

namespace UpDivA

open ReciprocityTheory.L2DbarEstimates MeasureTheory Topology ReciprocityTheory.ChartRestriction.G.AR.Up.HE
open scoped ContDiff ENNReal

variable {n : ℕ} {U : Set (V n)}

theorem holo_val {f : V n → ℂ} (hf : DifferentiableOn ℂ f U) :
    Holo n (Subtype.val : U → V n) (fun x => f x.1) := by
  intro e he
  have hsub : e.target ⊆ U := by
    intro y hy
    rw [← chart_z_symm n Subtype.val e he y hy]
    exact (e.symm y).2
  refine (hf.mono hsub).congr (fun y hy => ?_)
  show f (e.symm y).1 = f y
  rw [chart_z_symm n Subtype.val e he y hy]

theorem skoda_open (hU : IsOpen U) (S : EtaleStein n U) (hz : S.z = Subtype.val) {p : ℕ}
    (g : Fin p → V n → ℂ) (ph0 : V n → ℝ) (t : ℝ) (f : V n → ℂ) (hp : 2 ≤ p)
    (hg : ∀ i, DifferentiableOn ℂ (g i) U) (hnz : ∀ y ∈ U, ∃ i, g i y ≠ 0)
    (hph : ContDiffOn ℝ ∞ ph0 U)
    (hl : ∀ y ∈ U, ∀ ξ : Fin n → ℂ, 0 ≤ (leviV n (fun w => (ph0 w : ℂ)) y ξ).re)
    (ht : (p : ℝ) - 1 < t) (hf : DifferentiableOn ℂ f U)
    (hI : ∫⁻ y in U, ENNReal.ofReal (‖f y‖ ^ 2 * (∑ i, ‖g i y‖ ^ 2) ^ (-(t + 1)) * Real.exp (-ph0 y)) < ⊤) :
    ∃ hh : Fin p → V n → ℂ, (∀ i, DifferentiableOn ℂ (hh i) U) ∧
      (∀ y ∈ U, f y = ∑ i, g i y * hh i y) ∧
      ∫⁻ y in U, ENNReal.ofReal ((∑ i, ‖hh i y‖ ^ 2) * (∑ i, ‖g i y‖ ^ 2) ^ (-t) * Real.exp (-ph0 y)) ≤
        ENNReal.ofReal (t / (t - ((p : ℝ) - 1))) *
          ∫⁻ y in U, ENNReal.ofReal (‖f y‖ ^ 2 * (∑ i, ‖g i y‖ ^ 2) ^ (-(t + 1)) * Real.exp (-ph0 y)) := by
  classical
  have hzl : IsLocalHomeomorph (Subtype.val : U → V n) := hz ▸ S.isLocalHomeomorph
  have hemb : MeasurableEmbedding (Subtype.val : U → V n) := MeasurableEmbedding.subtype_coe hU.measurableSet
  have hvol : vol n (Subtype.val : U → V n) = (volume : Measure (V n)).comap Subtype.val := by
    ext A hA
    rw [vol_image n Subtype.val hzl Set.univ isOpen_univ Subtype.val_injective.injOn A hA (Set.subset_univ _),
      hemb.comap_apply]
  have htgt : ∀ (e : OpenPartialHomeomorph U (V n)), IsChart n Subtype.val e → e.target ⊆ U := by
    intro e he y hy
    rw [← chart_z_symm n Subtype.val e he y hy]
    exact (e.symm y).2
  have hleviC : ∀ (g₁ g₂ : V n → ℂ) (y : V n), g₁ =ᶠ[𝓝 y] g₂ → ∀ ξ, leviV n g₁ y ξ = leviV n g₂ y ξ := by
    intro g₁ g₂ y h ξ
    unfold leviV
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    rw [wd_congr n j _ _ y (h.eventually_nhds.mono fun y' h' => wdb_congr n k g₁ g₂ y' h')]
  have hsm : SmoothR n S.z (fun x : U => ph0 x.1) := by
    rw [hz]
    intro e he
    have hc : ContDiffOn ℝ ∞ (fun y => ((ph0 y : ℝ) : ℂ)) U := Complex.ofRealCLM.contDiff.comp_contDiffOn hph
    refine (hc.mono (htgt e he)).congr (fun y hy => ?_)
    show ((ph0 (e.symm y).1 : ℝ) : ℂ) = ((ph0 y : ℝ) : ℂ)
    rw [chart_z_symm n Subtype.val e he y hy]
  have hlev : LeviNonneg n S.z (fun x : U => ph0 x.1) := by
    rw [hz]
    intro x ξ
    obtain ⟨e, he, hxe⟩ := exists_chart n Subtype.val hzl x
    rw [levi_eq_leviV n Subtype.val e he _ x hxe ξ]
    have heq : (fun y => ((ph0 (e.symm y).1 : ℝ) : ℂ)) =ᶠ[𝓝 x.1] fun y => ((ph0 y : ℝ) : ℂ) := by
      have hxt : x.1 ∈ e.target := by
        rw [he hxe]
        exact e.map_source hxe
      filter_upwards [e.open_target.mem_nhds hxt] with y hy
      rw [chart_z_symm n Subtype.val e he y hy]
    rw [hleviC _ _ _ heq ξ]
    exact hl x.1 x.2 ξ
  have hI' : ∫⁻ x, ENNReal.ofReal (‖f x.1‖ ^ 2 * (∑ i, ‖g i x.1‖ ^ 2) ^ (-(t + 1)) * Real.exp (-ph0 x.1)) ∂vol n S.z < ⊤ := by
    rw [hz, hvol, lintegral_subtype_comap hU.measurableSet
      (fun y => ENNReal.ofReal (‖f y‖ ^ 2 * (∑ i, ‖g i y‖ ^ 2) ^ (-(t + 1)) * Real.exp (-ph0 y)))]
    exact hI
  obtain ⟨hh, hhH, hhf, hhI⟩ := skoda n U S p (fun i x => g i x.1) (fun x => ph0 x.1) t (fun x => f x.1) hp
    (fun i => by rw [hz]; exact holo_val (hg i)) (fun x => hnz x.1 x.2) hsm hlev ht (by rw [hz]; exact holo_val hf) hI'
  refine ⟨fun i y => if h : y ∈ U then hh i ⟨y, h⟩ else 0, fun i y hy => ?_, fun y hy => ?_, ?_⟩
  · obtain ⟨e, he, hxe⟩ := exists_chart n Subtype.val hzl ⟨y, hy⟩
    have hH : DifferentiableOn ℂ (hh i ∘ e.symm) e.target := by
      have := hhH i
      rw [hz] at this
      exact this e he
    have hyt : y ∈ e.target := by
      have h1 : e ⟨y, hy⟩ = y := (he hxe).symm
      rw [← h1]
      exact e.map_source hxe
    have hD := (hH y hyt).differentiableAt (e.open_target.mem_nhds hyt)
    refine (hD.congr_of_eventuallyEq ?_).differentiableWithinAt
    filter_upwards [e.open_target.mem_nhds hyt] with w hw
    have hwU : w ∈ U := htgt e he hw
    rw [dite_eq_left hwU]
    show hh i ⟨w, hwU⟩ = hh i (e.symm w)
    congr 1
    exact Subtype.ext (chart_z_symm n Subtype.val e he w hw).symm
  · have := hhf ⟨y, hy⟩
    simpa [hy] using this
  · have hL : ∫⁻ y in U, ENNReal.ofReal ((∑ i, ‖(if h : y ∈ U then hh i ⟨y, h⟩ else 0)‖ ^ 2) *
        (∑ i, ‖g i y‖ ^ 2) ^ (-t) * Real.exp (-ph0 y)) =
        ∫⁻ x, ENNReal.ofReal ((∑ i, ‖hh i x‖ ^ 2) * (∑ i, ‖g i x.1‖ ^ 2) ^ (-t) * Real.exp (-ph0 x.1)) ∂vol n S.z := by
      rw [hz, hvol, ← lintegral_subtype_comap hU.measurableSet]
      refine lintegral_congr fun x => ?_
      simp [x.2]
    have hR : ∫⁻ y in U, ENNReal.ofReal (‖f y‖ ^ 2 * (∑ i, ‖g i y‖ ^ 2) ^ (-(t + 1)) * Real.exp (-ph0 y)) =
        ∫⁻ x, ENNReal.ofReal (‖f x.1‖ ^ 2 * (∑ i, ‖g i x.1‖ ^ 2) ^ (-(t + 1)) * Real.exp (-ph0 x.1)) ∂vol n S.z := by
      rw [hz, hvol, lintegral_subtype_comap hU.measurableSet
        (fun y => ENNReal.ofReal (‖f y‖ ^ 2 * (∑ i, ‖g i y‖ ^ 2) ^ (-(t + 1)) * Real.exp (-ph0 y)))]
    rw [hL, hR]
    exact hhI

end UpDivA

end ReciprocityTheory.ChartRestriction.G.AR.Up
end

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

namespace UpDivB

open ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal

variable {n : ℕ} {U : Set (V n)}

theorem norm_sum_sq_le {ι : Type*} (s : Finset ι) (x : ι → ℂ) :
    ‖∑ i ∈ s, x i‖ ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖x i‖ ^ 2 := by
  calc ‖∑ i ∈ s, x i‖ ^ 2 ≤ (∑ i ∈ s, ‖x i‖) ^ 2 := by
        gcongr
        exact norm_sum_le _ _
    _ ≤ s.card * ∑ i ∈ s, ‖x i‖ ^ 2 := sq_sum_le_card_mul_sum_sq

def stp {p : ℕ} (α : Fin p → ℕ) (k : Fin p) : Fin p → ℕ := fun i => α i + if i = k then 1 else 0

theorem mem_step {p N : ℕ} {α : Fin p → ℕ} (hα : α ∈ Finset.Nat.antidiagonalTuple p N) (k : Fin p) :
    stp α k ∈ Finset.Nat.antidiagonalTuple p (N + 1) := by
  rw [Finset.Nat.mem_antidiagonalTuple] at hα ⊢
  simp [stp, Finset.sum_add_distrib, hα]

theorem pow_step {p : ℕ} (g : Fin p → ℂ) (α : Fin p → ℕ) (k : Fin p) :
    ∏ i, g i ^ stp α k i = (∏ i, g i ^ α i) * g k := by
  simp only [stp, pow_add, Finset.prod_mul_distrib]
  congr 1
  have h : ∀ i, g i ^ (if i = k then 1 else 0) = if i = k then g i else 1 := by
    intro i; split_ifs <;> simp
  simp only [h, Finset.prod_ite_eq', Finset.mem_univ, if_true]

theorem iter_div (hU : IsOpen U) (S : EtaleStein n U) (hz : S.z = Subtype.val) {p : ℕ}
    (g : Fin p → V n → ℂ) (ph0 : V n → ℝ) (hp : 2 ≤ p)
    (hg : ∀ i, DifferentiableOn ℂ (g i) U) (hnz : ∀ y ∈ U, ∃ i, g i y ≠ 0)
    (hph : ContDiffOn ℝ ∞ ph0 U)
    (hl : ∀ y ∈ U, ∀ ξ : Fin n → ℂ, 0 ≤ (leviV n (fun w => (ph0 w : ℂ)) y ξ).re)
    (τ0 : ℝ) : ∀ (N : ℕ), (p : ℝ) - 1 < τ0 - N - 1 + 1 →
    ∀ F : V n → ℂ, DifferentiableOn ℂ F U →
    ∫⁻ y in U, ENNReal.ofReal (‖F y‖ ^ 2 * (∑ i, ‖g i y‖ ^ 2) ^ (-τ0) * Real.exp (-ph0 y)) < ⊤ →
    ∃ H : (Fin p → ℕ) → V n → ℂ,
      (∀ α ∈ Finset.Nat.antidiagonalTuple p N, DifferentiableOn ℂ (H α) U ∧
        ∫⁻ y in U, ENNReal.ofReal (‖H α y‖ ^ 2 * (∑ i, ‖g i y‖ ^ 2) ^ (-(τ0 - N)) *
          Real.exp (-ph0 y)) < ⊤) ∧
      ∀ y ∈ U, F y = ∑ α ∈ Finset.Nat.antidiagonalTuple p N, (∏ i, g i y ^ α i) * H α y := by
  have hSpos : ∀ y ∈ U, 0 < ∑ i, ‖g i y‖ ^ 2 := by
    intro y hy
    obtain ⟨i, hi⟩ := hnz y hy
    exact Finset.sum_pos' (fun _ _ => by positivity) ⟨i, Finset.mem_univ _, by positivity⟩
  have hScont : ContinuousOn (fun y => ∑ i, ‖g i y‖ ^ 2) U :=
    continuousOn_finsetSum _ fun i _ => ((hg i).continuousOn.norm).pow 2
  intro N
  induction N with
  | zero =>
    intro _ F hF hI
    refine ⟨fun _ => F, fun α hα => ⟨hF, by simpa using hI⟩, fun y _ => ?_⟩
    rw [Finset.Nat.antidiagonalTuple_zero_right]
    simp
  | succ N ih =>
    intro hN F hF hI
    have hN' : (p : ℝ) - 1 < τ0 - N - 1 + 1 := by push_cast at hN; linarith
    obtain ⟨H, hH, hid⟩ := ih hN' F hF hI
    set t : ℝ := τ0 - N - 1 with htdef
    have ht : (p : ℝ) - 1 < t := by rw [htdef]; push_cast at hN; linarith
    have hstep : ∀ α ∈ Finset.Nat.antidiagonalTuple p N, ∃ hh : Fin p → V n → ℂ,
        (∀ i, DifferentiableOn ℂ (hh i) U) ∧ (∀ y ∈ U, H α y = ∑ i, g i y * hh i y) ∧
        ∫⁻ y in U, ENNReal.ofReal ((∑ i, ‖hh i y‖ ^ 2) * (∑ i, ‖g i y‖ ^ 2) ^ (-t) *
          Real.exp (-ph0 y)) < ⊤ := by
      intro α hα
      have hIα : ∫⁻ y in U, ENNReal.ofReal (‖H α y‖ ^ 2 * (∑ i, ‖g i y‖ ^ 2) ^ (-(t + 1)) *
          Real.exp (-ph0 y)) < ⊤ := by
        have e : -(t + 1) = -(τ0 - N) := by rw [htdef]; ring
        rw [e]; exact (hH α hα).2
      obtain ⟨hh, hhd, hhid, hhest⟩ := UpDivA.skoda_open hU S hz g ph0 t (H α) hp hg hnz hph hl ht
        (hH α hα).1 hIα
      exact ⟨hh, hhd, hhid, lt_of_le_of_lt hhest (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hIα)⟩
    choose! hh hhd hhid hhI using hstep
    set A := Finset.Nat.antidiagonalTuple p N with hA
    obtain ⟨w, hw⟩ : ∃ w : V n → ℝ, w = fun y => (∑ i, ‖g i y‖ ^ 2) ^ (-t) * Real.exp (-ph0 y) :=
      ⟨_, rfl⟩
    have hw0 : ∀ y, 0 ≤ w y := fun y => by
      rw [hw]; exact mul_nonneg (Real.rpow_nonneg (Finset.sum_nonneg fun _ _ => by positivity) _)
        (Real.exp_pos _).le
    have hwc : ContinuousOn w U := by
      rw [hw]
      exact (hScont.rpow_const fun y hy => Or.inl (hSpos y hy).ne').mul
        (Real.continuous_exp.comp_continuousOn hph.continuousOn.neg)
    refine ⟨fun β y => ∑ α ∈ A, ∑ k, if stp α k = β then hh α k y else 0,
      fun β _ => ⟨?_, ?_⟩, ?_⟩
    · have hk : ∀ α ∈ A, ∀ k ∈ (Finset.univ : Finset (Fin p)),
          DifferentiableOn ℂ (fun y => if stp α k = β then hh α k y else 0) U := by
        intro α hα k _
        by_cases hk : stp α k = β
        · simp only [hk, if_true]; exact hhd α hα k
        · simp only [hk, if_false]; exact differentiableOn_const (c := (0 : ℂ))
      have hα : ∀ α ∈ A, DifferentiableOn ℂ
          (fun y => ∑ k, if stp α k = β then hh α k y else 0) U := fun α hα =>
        (DifferentiableOn.sum (u := Finset.univ) (A := fun k y => if stp α k = β then hh α k y else 0)
          (hk α hα)).congr fun y _ => by simp [Finset.sum_apply]
      exact (DifferentiableOn.sum (u := A)
        (A := fun α y => ∑ k, if stp α k = β then hh α k y else 0) hα).congr fun y _ => by
          simp [Finset.sum_apply]
    · set C : ℝ := ((A ×ˢ (Finset.univ : Finset (Fin p))).card : ℝ) with hC
      have hpt : ∀ y, ‖∑ α ∈ A, ∑ k, (if stp α k = β then hh α k y else 0)‖ ^ 2
          ≤ C * ∑ α ∈ A, ∑ k, ‖hh α k y‖ ^ 2 := by
        intro y
        rw [← Finset.sum_product']
        refine (norm_sum_sq_le _ _).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
        rw [Finset.sum_product]
        refine Finset.sum_le_sum fun α _ => Finset.sum_le_sum fun k _ => ?_
        split_ifs
        · exact le_rfl
        · simp
      have hbound : ∀ y, ENNReal.ofReal (‖∑ α ∈ A, ∑ k, (if stp α k = β then hh α k y else 0)‖ ^ 2
          * w y) ≤ ENNReal.ofReal C * ∑ α ∈ A, ENNReal.ofReal ((∑ k, ‖hh α k y‖ ^ 2) * w y) := by
        intro y
        rw [← ENNReal.ofReal_sum_of_nonneg (fun α _ => mul_nonneg (Finset.sum_nonneg fun _ _ =>
          by positivity) (hw0 y)), ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        calc ‖∑ α ∈ A, ∑ k, (if stp α k = β then hh α k y else 0)‖ ^ 2 * w y
            ≤ (C * ∑ α ∈ A, ∑ k, ‖hh α k y‖ ^ 2) * w y := mul_le_mul_of_nonneg_right (hpt y) (hw0 y)
          _ = C * ∑ α ∈ A, (∑ k, ‖hh α k y‖ ^ 2) * w y := by rw [mul_assoc, Finset.sum_mul]
      have hfin : ∫⁻ y in U, ENNReal.ofReal C * ∑ α ∈ A, ENNReal.ofReal ((∑ k, ‖hh α k y‖ ^ 2) * w y)
          < ⊤ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
        rw [lintegral_finsetSum']
        · refine ENNReal.sum_lt_top.mpr fun α hα => ?_
          have := hhI α hα
          rw [hw]
          simpa [mul_assoc] using this
        · intro α hα
          have hc : ContinuousOn (fun y => (∑ k, ‖hh α k y‖ ^ 2) * w y) U :=
            (continuousOn_finsetSum _ fun k _ => ((hhd α hα k).continuousOn.norm).pow 2).mul hwc
          exact (ENNReal.continuous_ofReal.comp_continuousOn hc).aemeasurable hU.measurableSet
      have e2 : (fun y => ENNReal.ofReal (‖∑ α ∈ A, ∑ k, (if stp α k = β then hh α k y else 0)‖ ^ 2 *
          (∑ i, ‖g i y‖ ^ 2) ^ (-(τ0 - ((N + 1 : ℕ) : ℝ))) * Real.exp (-ph0 y))) =
          fun y => ENNReal.ofReal (‖∑ α ∈ A, ∑ k, (if stp α k = β then hh α k y else 0)‖ ^ 2 * w y) := by
        funext y
        rw [hw, mul_assoc]
        congr 4
        rw [htdef]; push_cast; ring
      show ∫⁻ y in U, ENNReal.ofReal (‖∑ α ∈ A, ∑ k, (if stp α k = β then hh α k y else 0)‖ ^ 2 *
          (∑ i, ‖g i y‖ ^ 2) ^ (-(τ0 - ((N + 1 : ℕ) : ℝ))) * Real.exp (-ph0 y)) < ⊤
      rw [e2]
      exact lt_of_le_of_lt (lintegral_mono hbound) hfin
    · intro y hy
      rw [hid y hy]
      have h1 : ∀ α ∈ A, (∏ i, g i y ^ α i) * H α y =
          ∑ k, (∏ i, g i y ^ stp α k i) * hh α k y := by
        intro α hα
        rw [hhid α hα y hy, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [pow_step]; ring
      rw [Finset.sum_congr rfl h1]
      symm
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun α hα => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [mul_ite, mul_zero]
      rw [Finset.sum_ite_eq, if_pos (mem_step hα k)]

end UpDivB

end ReciprocityTheory.ChartRestriction.G.AR.Up
end

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

namespace UpDivC

open ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Metric Set Filter

variable {n : ℕ}

theorem dense_nonzero {U : Set (V n)} (hU : IsOpen U) (hUc : IsPreconnected U) {g : V n → ℂ}
    (hg : DifferentiableOn ℂ g U) (hg0 : ∃ z ∈ U, g z ≠ 0) {z : V n} (hz : z ∈ U) :
    ∃ᶠ y in 𝓝 z, y ∈ U ∧ g y ≠ 0 := by
  by_contra hcon
  rw [Filter.not_frequently] at hcon
  have hz0 : ∀ᶠ y in 𝓝 z, g y = 0 := by
    filter_upwards [hcon, hU.mem_nhds hz] with y hy hyU
    by_contra h
    exact hy ⟨hyU, h⟩
  have hsub : U ⊆ {y | ∀ᶠ x in 𝓝 y, g x = 0} := by
    refine hUc.subset_of_closure_inter_subset isOpen_setOf_eventually_nhds ⟨z, hz, hz0⟩ ?_
    rintro y ⟨hycl, hyU⟩
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU y hyU
    obtain ⟨b, hb, hdist⟩ := Metric.mem_closure_iff.mp hycl ε hε
    have hbb : b ∈ ball y ε := by
      rw [mem_ball, dist_comm]
      exact hdist
    have hEq := ReciprocityTheory.L2DbarEstimates.C.ident n (ball y ε) g b isOpen_ball (convex_ball y ε)
      (hg.mono hball) hbb hb
    exact Filter.eventually_of_mem (ball_mem_nhds y hε) (fun w hw => by simpa using hEq hw)
  obtain ⟨w, hwU, hw⟩ := hg0
  exact hw (hsub hwU).self_of_nhds

theorem ext_glue {U : Set (V n)} (hU : IsOpen U) (hUc : IsPreconnected U) {g : V n → ℂ}
    (hg : DifferentiableOn ℂ g U) (hg0 : ∃ z ∈ U, g z ≠ 0) {H : V n → ℂ}
    (hH : DifferentiableOn ℂ H (U ∩ {z | g z ≠ 0}))
    (hloc : ∀ z ∈ U, ∃ r > 0, ball z r ⊆ U ∧
      IntegrableOn (fun y => ‖H y‖ ^ 2) (ball z r \ {y | g y = 0})) :
    ∃ H' : V n → ℂ, DifferentiableOn ℂ H' U ∧ EqOn H' H (U ∩ {z | g z ≠ 0}) := by
  classical
  choose! r hr hrU hint using hloc

  have hE : ∀ z ∈ U, ∃ E : V n → ℂ, DifferentiableOn ℂ E (ball z (r z)) ∧
      EqOn E H (ball z (r z) \ {y | g y = 0}) := by
    intro z hz
    exact ReciprocityTheory.L2DbarEstimates.C.ext n (ball z (r z)) g H isOpen_ball (hg.mono (hrU z hz))
      (hH.mono (fun y hy => ⟨hrU z hz hy.1, hy.2⟩)) (hint z hz)
  choose! E hEd hEe using hE

  have hagree : ∀ y ∈ U, ∀ z ∈ U, ∀ w ∈ ball y (r y) ∩ ball z (r z), E y w = E z w := by
    intro y hy z hz w hw
    have hwU : w ∈ U := hrU y hy hw.1
    have hopen : IsOpen (ball y (r y) ∩ ball z (r z)) := isOpen_ball.inter isOpen_ball
    have hc1 : ContinuousAt (E y) w :=
      (hEd y hy).continuousOn.continuousAt (isOpen_ball.mem_nhds hw.1)
    have hc2 : ContinuousAt (E z) w :=
      (hEd z hz).continuousOn.continuousAt (isOpen_ball.mem_nhds hw.2)
    have hfreq : ∃ᶠ v in 𝓝 w, E y v - E z v ∈ ({0} : Set ℂ) := by
      have h1 := (dense_nonzero hU hUc hg hg0 hwU).and_eventually
        (hopen.mem_nhds hw : ∀ᶠ v in 𝓝 w, v ∈ ball y (r y) ∩ ball z (r z))
      refine h1.mono ?_
      rintro v ⟨⟨-, hgv⟩, hv1, hv2⟩
      rw [Set.mem_singleton_iff, sub_eq_zero, hEe y hy ⟨hv1, hgv⟩, hEe z hz ⟨hv2, hgv⟩]
    have h0 := isClosed_singleton.mem_of_frequently_of_tendsto hfreq (hc1.sub hc2)
    simpa [sub_eq_zero] using h0
  refine ⟨fun w => E w w, ?_, ?_⟩
  · intro z hz
    have hev : (fun w => E w w) =ᶠ[𝓝 z] E z := by
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_self (hr z hz)), hU.mem_nhds hz]
        with w hw hwU
      exact hagree w hwU z hz w ⟨mem_ball_self (hr w hwU), hw⟩
    exact (((hEd z hz).differentiableAt
      (isOpen_ball.mem_nhds (mem_ball_self (hr z hz)))).congr_of_eventuallyEq hev).differentiableWithinAt
  · rintro w ⟨hwU, hgw⟩
    exact hEe w hwU ⟨mem_ball_self (hr w hwU), hgw⟩

end UpDivC

end ReciprocityTheory.ChartRestriction.G.AR.Up
end

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

namespace UpDivF

open ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Metric Set Filter
open scoped ENNReal

variable {n : ℕ}

private theorem countable_of_forall_exists_gap_above (S : Set ℝ) (h : ∀ t ∈ S, ∃ y, t < y ∧ ∀ u ∈ S, ¬ (t < u ∧ u < y)) :
    S.Countable := by
  classical
  have hq : ∀ t ∈ S, ∃ q : ℚ, t < q ∧ ∀ u ∈ S, ¬ (t < u ∧ u < q) := by
    intro t ht
    obtain ⟨y, hy, hyS⟩ := h t ht
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hy
    exact ⟨q, hq1, fun u hu h' => hyS u hu ⟨h'.1, h'.2.trans hq2⟩⟩
  choose! f hf1 hf2 using hq
  refine Set.MapsTo.countable_of_injOn (f := f) (Set.mapsTo_univ f S) ?_ Set.countable_univ
  intro a ha b hb hab
  by_contra hne
  rcases lt_or_gt_of_ne hne with h1 | h1
  · exact hf2 a ha b hb ⟨h1, by rw [hab]; exact hf1 b hb⟩
  · exact hf2 b hb a ha ⟨h1, by rw [← hab]; exact hf1 a ha⟩

private theorem volume_ball_inter_zeroSet_eq_zero_of_ne_zero {U : Set (V n)} {g : V n → ℂ} (hg : DifferentiableOn ℂ g U) {z0 : V n}
    {R R' : ℝ} (hR' : 0 < R') (hRR : R' < R) (hball : ball z0 R ⊆ U) (hz0 : g z0 ≠ 0) :
    volume (ball z0 R' ∩ {z | g z = 0}) = 0 := by
  have hR : 0 < R := hR'.trans hRR
  have hcs : ∀ (u : ℝ) (w : V n), ((u : ℂ) • w) = u • w := fun u w => by
    first
      | exact Complex.coe_smul u w
      | exact (RCLike.real_smul_eq_coe_smul (K := ℂ) u w).symm
  have hmaps : ∀ t : ℝ, ∀ x : V n, t ∈ Ioo (0:ℝ) 1 → x ∈ ball z0 R →
      z0 + t • (x - z0) ∈ ball z0 R := by
    intro t x ht hx
    rw [Metric.mem_ball, dist_eq_norm] at hx ⊢
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht.1]
    nlinarith [mul_nonneg (sub_nonneg.2 ht.2.le) (norm_nonneg (x - z0))]
  have hO1 : IsOpen (Ioo (0:ℝ) 1 ×ˢ ball z0 R) := isOpen_Ioo.prod isOpen_ball
  have hFc : ContinuousOn (fun p : ℝ × V n => g (z0 + p.1 • (p.2 - z0))) (Ioo (0:ℝ) 1 ×ˢ ball z0 R) :=
    hg.continuousOn.comp (f := fun p : ℝ × V n => z0 + p.1 • (p.2 - z0))
      (Continuous.continuousOn (by fun_prop)) (fun p hp => hball (hmaps p.1 p.2 hp.1 hp.2))
  have hOpen := hFc.isOpen_inter_preimage hO1 (isOpen_compl_singleton (x := (0:ℂ)))
  obtain ⟨A, hAdef⟩ : ∃ A : Set (ℝ × V n), A = (Ioo (0:ℝ) 1 ×ˢ ball z0 R) \
      ((Ioo (0:ℝ) 1 ×ˢ ball z0 R) ∩ (fun p : ℝ × V n => g (z0 + p.1 • (p.2 - z0))) ⁻¹' {(0:ℂ)}ᶜ) :=
    ⟨_, rfl⟩
  have hA : MeasurableSet A := by
    rw [hAdef]
    exact hO1.measurableSet.diff hOpen.measurableSet
  have memA : ∀ t x, (t, x) ∈ A ↔ t ∈ Ioo (0:ℝ) 1 ∧ x ∈ ball z0 R ∧ g (z0 + t • (x - z0)) = 0 := by
    intro t x
    rw [hAdef]
    simp only [Set.mem_diff, Set.mem_inter_iff, Set.mem_prod, Set.mem_preimage, Set.mem_compl_iff,
      Set.mem_singleton_iff]
    tauto
  have hslice : ∀ x : V n, volume ((fun t : ℝ => (t, x)) ⁻¹' A) = 0 := by
    intro x
    by_cases hx : x ∈ ball z0 R
    · set v := x - z0 with hv
      have hvR : ‖v‖ < R := by
        rw [hv, ← dist_eq_norm]
        exact hx
      have hmpos : 0 < max ‖v‖ (R / 2) := lt_max_of_lt_right (by linarith)
      have hmR : max ‖v‖ (R / 2) < R := max_lt hvR (by linarith)
      set ρ := R / max ‖v‖ (R / 2) with hρ
      have hρ1 : 1 < ρ := (one_lt_div hmpos).mpr hmR
      have hDmaps : ∀ s ∈ ball (0:ℂ) ρ, z0 + s • v ∈ U := by
        intro s hs
        apply hball
        rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul]
        rw [Metric.mem_ball, dist_zero_right] at hs
        calc ‖s‖ * ‖v‖ ≤ ‖s‖ * max ‖v‖ (R / 2) :=
              mul_le_mul_of_nonneg_left (le_max_left _ _) (norm_nonneg _)
          _ < ρ * max ‖v‖ (R / 2) := mul_lt_mul_of_pos_right hs hmpos
          _ = R := div_mul_cancel₀ _ hmpos.ne'
      have hφd : DifferentiableOn ℂ (fun s : ℂ => g (z0 + s • v)) (ball (0:ℂ) ρ) :=
        hg.comp (f := fun s : ℂ => z0 + s • v) (Differentiable.differentiableOn (by fun_prop)) hDmaps
      have hφa := hφd.analyticOnNhd isOpen_ball
      have h0D : (0:ℂ) ∈ ball (0:ℂ) ρ := Metric.mem_ball_self (by linarith)
      have hφ0 : g (z0 + (0:ℂ) • v) ≠ 0 := by
        rw [zero_smul, add_zero]
        exact hz0
      have hpre : IsPreconnected (ball (0:ℂ) ρ) := (convex_ball (0:ℂ) ρ).isPreconnected
      have hiso : ∀ t : ℝ, t ∈ Ioo (0:ℝ) 1 →
          ∃ ε > 0, ∀ u : ℝ, t < u → u < t + ε → g (z0 + u • v) ≠ 0 := by
        intro t ht
        have htD : (t:ℂ) ∈ ball (0:ℂ) ρ := by
          rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht.1]
          linarith [ht.2]
        have hev : ∀ᶠ s in 𝓝[≠] (t:ℂ), g (z0 + s • v) ≠ 0 := by
          by_contra hne
          rw [Filter.not_eventually] at hne
          simp only [not_not] at hne
          have h5 := hφa.eqOn_zero_of_preconnected_of_frequently_eq_zero hpre htD hne h0D
          exact hφ0 h5
        obtain ⟨ε, hε, hεp⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hev)
        refine ⟨ε, hε, fun u hu1 hu2 => ?_⟩
        have h6 := hεp (y := (u:ℂ)) ?_ ?_
        · rwa [hcs] at h6
        · rw [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (by linarith)]
          linarith
        · exact fun h => (ne_of_gt hu1) (Complex.ofReal_injective h)
      have hcount : Set.Countable {t : ℝ | t ∈ Ioo (0:ℝ) 1 ∧ g (z0 + t • v) = 0} := by
        refine countable_of_forall_exists_gap_above _ fun t ht => ?_
        obtain ⟨ε, hε, hεp⟩ := hiso t ht.1
        exact ⟨t + ε, by linarith, fun u hu h' => hεp u h'.1 h'.2 hu.2⟩
      have hsub : (fun t : ℝ => (t, x)) ⁻¹' A ⊆ {t : ℝ | t ∈ Ioo (0:ℝ) 1 ∧ g (z0 + t • v) = 0} := by
        intro t ht
        have h7 := (memA t x).mp ht
        exact ⟨h7.1, h7.2.2⟩
      exact measure_mono_null hsub (hcount.measure_zero _)
    · have h8 : (fun t : ℝ => (t, x)) ⁻¹' A = ∅ :=
        Set.subset_empty_iff.mp (fun t ht => (hx ((memA t x).mp ht).2.1).elim)
      rw [h8, measure_empty]
  have hprod : (volume.prod volume : Measure (ℝ × V n)) A = 0 := by
    rw [Measure.prod_apply_symm hA]
    simp only [hslice, lintegral_zero]
  rw [Measure.prod_apply hA] at hprod
  have hlow : ∀ t ∈ Ioo (R' / R) 1,
      volume (ball z0 R' ∩ {z | g z = 0}) ≤ volume (Prod.mk t ⁻¹' A) := by
    intro t ht
    have ht0 : 0 < t := lt_trans (div_pos hR' hR) ht.1
    have htR : R' < t * R := (div_lt_iff₀ hR).mp ht.1
    have hsub : (fun x : V n => x - z0) ⁻¹' ((fun y : V n => t • y) ⁻¹'
        ((fun w : V n => z0 + w) ⁻¹' (ball z0 R' ∩ {z | g z = 0}))) ⊆ Prod.mk t ⁻¹' A := by
      intro x hx
      simp only [Set.mem_preimage] at hx
      rw [Set.mem_preimage, memA]
      refine ⟨⟨ht0, ht.2⟩, ?_, hx.2⟩
      have h1 := hx.1
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos ht0] at h1
      rw [Metric.mem_ball, dist_eq_norm]
      exact lt_of_mul_lt_mul_left (h1.trans htR) ht0.le
    have hti : 1 ≤ t⁻¹ := by
      have h2 := mul_inv_cancel₀ ht0.ne'
      nlinarith [mul_pos (inv_pos.mpr ht0) (sub_pos.mpr ht.2)]
    have hmeas : volume (ball z0 R' ∩ {z | g z = 0}) ≤ volume ((fun x : V n => x - z0) ⁻¹'
        ((fun y : V n => t • y) ⁻¹' ((fun w : V n => z0 + w) ⁻¹' (ball z0 R' ∩ {z | g z = 0})))) := by
      rw [show (fun x : V n => x - z0) = (fun x => x + -z0) from funext fun x => sub_eq_add_neg x z0,
        measure_preimage_add_right, Set.preimage_smul₀ ht0.ne', Measure.addHaar_smul,
        measure_preimage_add]
      refine le_mul_of_one_le_left (by positivity) ?_
      rw [← ENNReal.ofReal_one]
      apply ENNReal.ofReal_le_ofReal
      rw [abs_of_pos (pow_pos (inv_pos.mpr ht0) _)]
      first
        | exact one_le_pow₀ hti
        | exact one_le_pow_of_one_le' hti _
    exact hmeas.trans (measure_mono hsub)
  have hind : ∀ t, (Ioo (R' / R) 1).indicator (fun _ => volume (ball z0 R' ∩ {z | g z = 0})) t ≤
      volume (Prod.mk t ⁻¹' A) := by
    intro t
    by_cases ht : t ∈ Ioo (R' / R) 1
    · rw [Set.indicator_apply, if_pos ht]
      exact hlow t ht
    · rw [Set.indicator_apply, if_neg ht]
      positivity
  have hle : ∫⁻ t, (Ioo (R' / R) 1).indicator (fun _ => volume (ball z0 R' ∩ {z | g z = 0})) t ≤
      ∫⁻ t, volume (Prod.mk t ⁻¹' A) := lintegral_mono hind
  rw [lintegral_indicator_const measurableSet_Ioo, Real.volume_Ioo, hprod] at hle
  have hpos : ENNReal.ofReal (1 - R' / R) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le, sub_pos, div_lt_one hR]
    exact hRR
  exact (mul_eq_zero.mp (le_zero_iff.mp hle)).resolve_right hpos

theorem zero_null {U : Set (V n)} (hU : IsOpen U) (hUc : IsPreconnected U) {g : V n → ℂ}
    (hg : DifferentiableOn ℂ g U) (hg0 : ∃ z ∈ U, g z ≠ 0) :
    volume (U ∩ {z | g z = 0}) = 0 := by
  classical
  have hWopen : IsOpen {z : V n | ∀ᶠ y in 𝓝 z, g y = 0} := isOpen_setOf_eventually_nhds
  have hclosed : ∀ z ∈ U, z ∈ closure {z : V n | ∀ᶠ y in 𝓝 z, g y = 0} → ∀ᶠ y in 𝓝 z, g y = 0 := by
    intro z hz hzc
    obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hU z hz
    by_contra hne
    have hex : ∃ z0 ∈ ball z (r / 4), g z0 ≠ 0 := by
      by_contra h
      push_neg at h
      exact hne (Metric.eventually_nhds_iff_ball.mpr ⟨r / 4, by linarith, h⟩)
    obtain ⟨z0, hz0, hgz0⟩ := hex
    rw [Metric.mem_ball] at hz0
    have hball : ball z0 (3 * r / 4) ⊆ U := by
      intro y hy
      apply hrU
      rw [Metric.mem_ball] at hy ⊢
      linarith [dist_triangle y z0 z]
    have hnull := volume_ball_inter_zeroSet_eq_zero_of_ne_zero hg (R := 3 * r / 4) (R' := 5 * r / 8) (by linarith) (by linarith) hball hgz0
    obtain ⟨w, hwW, hwz⟩ := Metric.mem_closure_iff.mp hzc (r / 4) (by linarith)
    obtain ⟨δ, hδ, hδw⟩ := Metric.eventually_nhds_iff_ball.mp hwW
    have hsub : ball w (min δ (r / 8)) ⊆ ball z0 (5 * r / 8) ∩ {z | g z = 0} := by
      intro y hy
      rw [Metric.mem_ball] at hy
      have hy1 : dist y w < δ := lt_of_lt_of_le hy (min_le_left _ _)
      have hy2 : dist y w < r / 8 := lt_of_lt_of_le hy (min_le_right _ _)
      refine ⟨?_, hδw y hy1⟩
      rw [Metric.mem_ball]
      linarith [dist_triangle y w z, dist_triangle y z z0, dist_comm z0 z, dist_comm z w]
    exact (Metric.measure_ball_pos volume w (lt_min hδ (by linarith))).ne' (measure_mono_null hsub hnull)
  have hWempty : ∀ z ∈ U, ¬ ∀ᶠ y in 𝓝 z, g y = 0 := by
    have hdisj : Disjoint {z : V n | ∀ᶠ y in 𝓝 z, g y = 0} (closure {z : V n | ∀ᶠ y in 𝓝 z, g y = 0})ᶜ :=
      Set.disjoint_left.mpr fun a ha hb => hb (subset_closure ha)
    have hcover : U ⊆ {z : V n | ∀ᶠ y in 𝓝 z, g y = 0} ∪ (closure {z : V n | ∀ᶠ y in 𝓝 z, g y = 0})ᶜ := by
      intro z hz
      by_cases hc : z ∈ closure {z : V n | ∀ᶠ y in 𝓝 z, g y = 0}
      · exact Or.inl (hclosed z hz hc)
      · exact Or.inr hc
    rcases hUc.subset_or_subset hWopen isClosed_closure.isOpen_compl hdisj hcover with h | h
    · obtain ⟨z1, hz1U, hz1⟩ := hg0
      exact absurd (Filter.Eventually.self_of_nhds (h hz1U)) hz1
    · intro z hz hev
      exact h hz (subset_closure hev)
  apply measure_null_of_locally_null
  intro z hz
  obtain ⟨hzU, hgz⟩ := hz
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hU z hzU
  have hex : ∃ z0 ∈ ball z (r / 4), g z0 ≠ 0 := by
    by_contra h
    push_neg at h
    exact hWempty z hzU (Metric.eventually_nhds_iff_ball.mpr ⟨r / 4, by linarith, h⟩)
  obtain ⟨z0, hz0, hgz0⟩ := hex
  rw [Metric.mem_ball] at hz0
  have hball : ball z0 (3 * r / 4) ⊆ U := by
    intro y hy
    apply hrU
    rw [Metric.mem_ball] at hy ⊢
    linarith [dist_triangle y z0 z]
  have hnull := volume_ball_inter_zeroSet_eq_zero_of_ne_zero hg (R := 3 * r / 4) (R' := r / 2) (by linarith) (by linarith) hball hgz0
  refine ⟨(U ∩ {z | g z = 0}) ∩ ball z0 (r / 2), inter_mem_nhdsWithin _ (isOpen_ball.mem_nhds ?_), ?_⟩
  · rw [Metric.mem_ball, dist_comm]
    linarith
  · refine measure_mono_null ?_ hnull
    intro y hy
    exact ⟨hy.2, hy.1.2⟩

theorem eq_across {U : Set (V n)} (hU : IsOpen U) (hUc : IsPreconnected U) {g : V n → ℂ}
    (hg : DifferentiableOn ℂ g U) (hg0 : ∃ z ∈ U, g z ≠ 0) {f : V n → ℂ} (hf : ContinuousOn f U)
    (h0 : ∀ z ∈ U, g z ≠ 0 → f z = 0) : ∀ z ∈ U, f z = 0 := by
  intro z hz
  by_contra hfz
  have hnull := zero_null hU hUc hg hg0
  have hev : ∀ᶠ y in 𝓝 z, y ∈ U ∧ f y ≠ 0 :=
    Filter.Eventually.and (hU.mem_nhds hz : ∀ᶠ y in 𝓝 z, y ∈ U)
      ((hf.continuousAt (hU.mem_nhds hz)).eventually_ne hfz)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  have hsub : ball z ε ⊆ U ∩ {y | g y = 0} := fun y hy => by
    obtain ⟨hyU, hfy⟩ := hball y hy
    refine ⟨hyU, ?_⟩
    by_contra hgy
    exact hfy (h0 y hyU hgy)
  exact (Metric.measure_ball_pos volume z hε).ne' (measure_mono_null hsub hnull)

theorem loc_int {U U' : Set (V n)} (hU : IsOpen U) (hU'o : IsOpen U') {g : V n → ℂ}
    (hU' : ∀ y, y ∈ U' ↔ y ∈ U ∧ g y ≠ 0) {H : V n → ℂ} (hH : ContinuousOn H U')
    {ω : V n → ℝ} (hω : ∀ K ⊆ U, IsCompact K → ∃ c > 0, ∀ y ∈ K ∩ U', c ≤ ω y)
    (hI : ∫⁻ y in U', ENNReal.ofReal (‖H y‖ ^ 2 * ω y) < ⊤) :
    ∀ z ∈ U, ∃ r > 0, ball z r ⊆ U ∧ IntegrableOn (fun y => ‖H y‖ ^ 2) (ball z r \ {y | g y = 0}) := by
  intro z hz
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU z hz
  have hK : closedBall z (ε / 2) ⊆ U := (closedBall_subset_ball (by linarith)).trans hεU
  obtain ⟨c, hc, hcω⟩ := hω _ hK (isCompact_closedBall z (ε / 2))
  refine ⟨ε / 2, by linarith, ball_subset_closedBall.trans hK, ?_⟩
  have hS : ball z (ε / 2) \ {y | g y = 0} = ball z (ε / 2) ∩ U' := by
    ext y
    simp only [mem_diff, mem_inter_iff, mem_setOf_eq, hU']
    constructor
    · rintro ⟨hy, hgy⟩
      exact ⟨hy, hK (ball_subset_closedBall hy), hgy⟩
    · rintro ⟨hy, -, hgy⟩
      exact ⟨hy, hgy⟩
  rw [hS]
  have hSo : IsOpen (ball z (ε / 2) ∩ U') := isOpen_ball.inter hU'o
  have hSU : ball z (ε / 2) ∩ U' ⊆ U' := inter_subset_right
  have hcont : ContinuousOn (fun y => ‖H y‖ ^ 2) (ball z (ε / 2) ∩ U') :=
    ((hH.mono hSU).norm).pow 2
  have hmeas : AEMeasurable (fun y => ENNReal.ofReal (‖H y‖ ^ 2))
      (volume.restrict (ball z (ε / 2) ∩ U')) :=
    (ENNReal.continuous_ofReal.comp_continuousOn hcont).aemeasurable hSo.measurableSet
  have hbound : ∫⁻ y in ball z (ε / 2) ∩ U', ENNReal.ofReal (‖H y‖ ^ 2) ≠ ⊤ := by
    refine ne_of_lt (lt_of_le_of_lt ?_ (ENNReal.mul_lt_top (ENNReal.ofReal_lt_top : ENNReal.ofReal c⁻¹ < ⊤) hI))
    calc ∫⁻ y in ball z (ε / 2) ∩ U', ENNReal.ofReal (‖H y‖ ^ 2)
        ≤ ∫⁻ y in ball z (ε / 2) ∩ U', ENNReal.ofReal c⁻¹ * ENNReal.ofReal (‖H y‖ ^ 2 * ω y) := by
          refine setLIntegral_mono' hSo.measurableSet fun y hy => ?_
          rw [← ENNReal.ofReal_mul (inv_nonneg.2 hc.le)]
          refine ENNReal.ofReal_le_ofReal ?_
          have hcy : c ≤ ω y := hcω y ⟨ball_subset_closedBall hy.1, hy.2⟩
          have h1 : 1 ≤ c⁻¹ * ω y := by
            rw [inv_mul_eq_div, one_le_div hc]
            exact hcy
          nlinarith [mul_nonneg (sq_nonneg ‖H y‖) (sub_nonneg.2 h1)]
      _ = ENNReal.ofReal c⁻¹ * ∫⁻ y in ball z (ε / 2) ∩ U', ENNReal.ofReal (‖H y‖ ^ 2 * ω y) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal c⁻¹ * ∫⁻ y in U', ENNReal.ofReal (‖H y‖ ^ 2 * ω y) :=
          by gcongr
  refine (integrable_toReal_of_lintegral_ne_top hmeas hbound).congr (ae_of_all _ fun y => ?_)
  exact ENNReal.toReal_ofReal (sq_nonneg _)

end UpDivF

end ReciprocityTheory.ChartRestriction.G.AR.Up
end

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField Complex Topology Filter MeasureTheory Set ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst
  ReciprocityTheory.L2DbarEstimates UpDivD
open scoped ENNReal ContDiff

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace UpDivG

variable {r : ℕ}

theorem sum_bdd (X : Data E r) (la : Wt X.Ψ r) {N : ℕ} (P : Fin N → Frame X.Ψ r → ℂ)
    (hP : ∀ k, X.IsBddSec la (P k)) : ∃ C : ℝ, ∀ x ∈ X.dom, ∑ k, X.pnorm la (P k) x ^ 2 ≤ C := by
  choose C hC using fun k => (hP k).2
  refine ⟨∑ k, C k ^ 2, fun x hx => Finset.sum_le_sum fun k _ => ?_⟩
  have h0 : 0 ≤ X.pnorm la (P k) x := by
    unfold ReciprocityTheory.ChartRestriction.G.FD.Data.pnorm
    exact mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun τ _ =>
      Finset.prod_nonneg fun i _ => Real.rpow_nonneg (norm_nonneg _) _)
  exact pow_le_pow_left₀ h0 (hC k x hx) 2

end UpDivG

theorem upDiv_holds : UpDivStatement (E := E) := by
  intro r X Xa Fl _ _ bb m _ hm hmar _ x0 ho F hF hIn
  classical
  have hU : IsOpen (OmF X x0) := OntoB.isOpen_OmF X x0
  have hUc : IsPreconnected (OmF X x0) := OFC.omFConn_of_cm r X x0 ho
  have hbm : bb ≤ m := by
    have : 0 ≤ bb ^ 2 * ((X.Ψ.card * min X.p0 (r - X.p0) : ℕ) : ℝ) := by positivity
    linarith
  have hn2 : 2 ≤ nd X := Xa.n_ge
  have hTn : nd X ≤ Xa.T := by have := Xa.T_ge; nlinarith
  have hInU := hIn
  unfold InAt at hInU
  rw [IW.muF_lintegral] at hInU
  obtain ⟨Cs, hCs⟩ := UpDivG.sum_bdd X Xa.L Fl.s (fun k => (Fl.s_van k).1.1)
  obtain ⟨Cw, hCw⟩ := UpDivG.sum_bdd X Xa.L Xa.w (fun k => (Xa.w_van k).1.1)
  by_cases hex : ∃ k, ∃ z ∈ OmF X x0, Fl.s k (cpt X x0 z) ≠ 0
  swap
  ·
    simp only [not_exists, not_and, not_not] at hex
    have hWtop : ∀ z ∈ OmF X x0, WSk X Xa Fl (cpt X x0 z) = ⊤ := by
      intro z hz
      have hp : cpt X x0 z ∈ X.dom := hz
      have hs0 : ∑ k, X.pnorm Xa.L (Fl.s k) (cpt X x0 z) ^ 2 = 0 := by
        refine Finset.sum_eq_zero fun k _ => ?_
        rw [pnorm_sq X hp, hex k z hz, norm_zero]; ring
      have hwp : 0 < ∑ k, X.pnorm Xa.L (Xa.w k) (cpt X x0 z) ^ 2 := by
        rw [sumL_eq X Xa x0 hz]; exact mul_pos (Real.exp_pos _) (Sw_pos X Xa x0 hz)
      unfold WSk
      rw [if_pos hp, hs0, zero_div, ENNReal.ofReal_zero, ENNReal.zero_rpow_of_neg (by
        have : (1 : ℝ) ≤ Xa.T := by exact_mod_cast (show 1 ≤ Xa.T by omega)
        linarith)]
      refine ENNReal.mul_top ?_
      exact mul_ne_zero (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
        (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hwp) ENNReal.ofReal_ne_top).ne'
    have hF0 : ∀ z ∈ OmF X x0, F z = 0 := by
      intro z0 hz0
      by_contra hne
      have hev1 : ∀ᶠ y in 𝓝 z0, y ∈ OmF X x0 := hU.mem_nhds hz0
      have hev : ∀ᶠ y in 𝓝 z0, y ∈ OmF X x0 ∧ F y ≠ 0 :=
        hev1.and ((hF.continuousOn.continuousAt (hU.mem_nhds hz0)).eventually_ne hne)
      obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev
      have hsub : Metric.ball z0 ε ⊆ OmF X x0 := fun y hy => (hball y hy).1
      have htop : ∫⁻ y in Metric.ball z0 ε, ENNReal.ofReal (densF X x0 y) *
          (ENNReal.ofReal (‖F y‖ ^ 2 / kaF X x0 bb y) * WSk X Xa Fl (cpt X x0 y)) = ⊤ := by
        rw [setLIntegral_congr_fun measurableSet_ball (g := fun _ => ⊤) fun y hy => ?_,
          setLIntegral_const, ENNReal.top_mul (Metric.measure_ball_pos volume z0 hε).ne']
        have hyO := hsub hy
        have ha : ENNReal.ofReal (densF X x0 y) ≠ 0 := (ENNReal.ofReal_pos.mpr (OntoB.densF_pos hyO)).ne'
        have hb : ENNReal.ofReal (‖F y‖ ^ 2 / kaF X x0 bb y) ≠ 0 := by
          refine (ENNReal.ofReal_pos.mpr (div_pos ?_ (Real.exp_pos _))).ne'
          have := (hball y hy).2; positivity
        rw [hWtop y hyO, ENNReal.mul_top hb, ENNReal.mul_top ha]
      have := lt_of_le_of_lt (lintegral_mono_set hsub) hInU
      rw [htop] at this
      exact lt_irrefl _ this
    refine ⟨fun _ _ => 0, fun α _ => ⟨differentiableOn_const _, ?_⟩, fun z hz => ?_⟩
    · unfold InAt; simp
    · rw [hF0 z hz]; simp

  obtain ⟨k1, z1, hz1, hk1⟩ := hex
  set g1 : V (nd X) → ℂ := fun z => Fl.s k1 (cpt X x0 z) with hg1def
  have hg1 : DifferentiableOn ℂ g1 (OmF X x0) := OntoB.hol_comp X x0 (Fl.s_van k1).1.1.1.1
  have hg10 : ∃ z ∈ OmF X x0, g1 z ≠ 0 := ⟨z1, hz1, hk1⟩
  set U' : Set (V (nd X)) := {z | z ∈ OmF X x0 ∧ g1 z ≠ 0} with hU'def
  have hU'o : IsOpen U' := ExG.isOpen_Om X x0 g1 hg1
  obtain ⟨S, hSz, -⟩ := exhaustG_holds r X x0 ho g1 hg1
  set sv : Fin (nd X) → V (nd X) → ℂ := fun k z => Fl.s k (cpt X x0 z) with hsv
  have hsvO : ∀ k, DifferentiableOn ℂ (sv k) (OmF X x0) := fun k =>
    OntoB.hol_comp X x0 (Fl.s_van k).1.1.1.1
  have hsvd : ∀ k, DifferentiableOn ℂ (sv k) U' := fun k => (hsvO k).mono fun z hz => hz.1
  have hnz : ∀ y ∈ U', ∃ i, sv i y ≠ 0 := fun y hy => ⟨k1, hy.2⟩
  have hph : ContDiffOn ℝ ∞ (ph0 X Xa x0 bb) U' :=
    (UpDivE.plurisubharmonicWeight_smooth X Xa x0 bb).mono fun z hz => hz.1
  have hl : ∀ y ∈ U', ∀ ξ : Fin (nd X) → ℂ,
      0 ≤ (leviV (nd X) (fun w => ((ph0 X Xa x0 bb w : ℝ) : ℂ)) y ξ).re :=
    fun y hy ξ => UpDivE.leviForm_weight_nonneg X Xa x0 bb hbm ho (hmar x0 ho) hy.1 ξ
  have hSs : ∀ y ∈ U', 0 < Ss X Xa Fl x0 y := fun y hy =>
    Finset.sum_pos' (fun _ _ => by positivity) ⟨k1, Finset.mem_univ _, by have := hy.2; positivity⟩
  have hI : ∫⁻ y in U', ENNReal.ofReal (‖F y‖ ^ 2 * (∑ i, ‖sv i y‖ ^ 2) ^ (-((Xa.T : ℝ) - 1 / 2)) *
      Real.exp (-ph0 X Xa x0 bb y)) < ⊤ := by
    refine lt_of_le_of_lt ?_ hInU
    calc ∫⁻ y in U', ENNReal.ofReal (‖F y‖ ^ 2 * (∑ i, ‖sv i y‖ ^ 2) ^ (-((Xa.T : ℝ) - 1 / 2)) *
          Real.exp (-ph0 X Xa x0 bb y))
        = ∫⁻ y in U', ENNReal.ofReal (densF X x0 y) *
            (ENNReal.ofReal (‖F y‖ ^ 2 / kaF X x0 bb y) * WSk X Xa Fl (cpt X x0 y)) := by
          refine setLIntegral_congr_fun hU'o.measurableSet fun y hy => ?_
          exact (wSk_eq X Xa Fl x0 bb hy.1 (hSs y hy) F).symm
      _ ≤ _ := lintegral_mono_set fun y hy => hy.1
  have hcond : ((nd X : ℕ) : ℝ) - 1 < (Xa.T : ℝ) - 1 / 2 - ((Xa.T - nd X : ℕ) : ℝ) - 1 + 1 := by
    rw [Nat.cast_sub hTn]; linarith
  obtain ⟨H, hH, hid⟩ := UpDivB.iter_div hU'o S hSz sv (ph0 X Xa x0 bb) hn2 hsvd hnz hph hl
    ((Xa.T : ℝ) - 1 / 2) (Xa.T - nd X) hcond F (hF.mono fun z hz => hz.1) hI
  have hexp : ((Xa.T : ℝ) - 1 / 2 - ((Xa.T - nd X : ℕ) : ℝ)) = (nd X : ℝ) - 1 / 2 := by
    rw [Nat.cast_sub hTn]; ring
  have hSc : ContinuousOn (Ss X Xa Fl x0) (OmF X x0) :=
    continuousOn_finsetSum _ fun k _ => ((hsvO k).continuousOn.norm).pow 2
  have hpc : ContinuousOn (ph0 X Xa x0 bb) (OmF X x0) := (UpDivE.plurisubharmonicWeight_smooth X Xa x0 bb).continuousOn
  have hω : ∀ K ⊆ OmF X x0, IsCompact K → ∃ c > 0, ∀ y ∈ K ∩ U',
      c ≤ (∑ i, ‖sv i y‖ ^ 2) ^ (-((nd X : ℝ) - 1 / 2)) * Real.exp (-ph0 X Xa x0 bb y) := by
    intro K hKU hK
    obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hSc.mono hKU)
    obtain ⟨P, hP⟩ := hK.exists_bound_of_continuousOn (hpc.mono hKU)
    refine ⟨(max M 1) ^ (-((nd X : ℝ) - 1 / 2)) * Real.exp (-P), by positivity, fun y hy => ?_⟩
    have hsy := hSs y hy.2
    have hle : Ss X Xa Fl x0 y ≤ max M 1 := by
      have := hM y hy.1
      rw [Real.norm_of_nonneg hsy.le] at this
      exact this.trans (le_max_left _ _)
    have ha : (0 : ℝ) ≤ (nd X : ℝ) - 1 / 2 := by
      have : (2 : ℝ) ≤ nd X := by exact_mod_cast hn2
      linarith
    have h1 : (max M 1) ^ (-((nd X : ℝ) - 1 / 2)) ≤ (Ss X Xa Fl x0 y) ^ (-((nd X : ℝ) - 1 / 2)) := by
      rw [Real.rpow_neg (by positivity), Real.rpow_neg hsy.le]
      exact inv_anti₀ (Real.rpow_pos_of_pos hsy _) (Real.rpow_le_rpow hsy.le hle ha)
    have h2 : Real.exp (-P) ≤ Real.exp (-ph0 X Xa x0 bb y) := by
      refine Real.exp_le_exp.mpr ?_
      have := hP y hy.1
      have := le_abs_self (ph0 X Xa x0 bb y)
      rw [Real.norm_eq_abs] at *
      linarith
    exact mul_le_mul h1 h2 (Real.exp_pos _).le (Real.rpow_nonneg hsy.le _)
  have hext : ∀ α ∈ Finset.Nat.antidiagonalTuple (nd X) (Xa.T - nd X), ∃ H' : V (nd X) → ℂ,
      DifferentiableOn ℂ H' (OmF X x0) ∧ EqOn H' (H α) U' := by
    intro α hα
    have hIα : ∫⁻ y in U', ENNReal.ofReal (‖H α y‖ ^ 2 *
        ((∑ i, ‖sv i y‖ ^ 2) ^ (-((nd X : ℝ) - 1 / 2)) * Real.exp (-ph0 X Xa x0 bb y))) < ⊤ := by
      have := (hH α hα).2
      rw [hexp] at this
      simpa only [mul_assoc] using this
    have hloc := UpDivF.loc_int hU hU'o (g := g1) (fun y => Iff.rfl) (hH α hα).1.continuousOn hω hIα
    exact UpDivC.ext_glue hU hUc hg1 hg10 (hH α hα).1 hloc
  choose! Hx hHxd hHxeq using hext
  refine ⟨Hx, fun α hα => ⟨hHxd α hα, ?_⟩, fun z hz => ?_⟩
  · unfold InAt
    rw [IW.muF_lintegral]
    have hnull := UpDivF.zero_null hU hUc hg1 hg10
    have hae : (OmF X x0 : Set (V (nd X))) =ᵐ[volume] U' := by
      refine ae_eq_set.mpr ⟨?_, ?_⟩
      · refine measure_mono_null (fun y hy => ?_) hnull
        refine ⟨hy.1, ?_⟩
        by_contra h
        exact hy.2 ⟨hy.1, h⟩
      · have : U' \ OmF X x0 = ∅ := by
          ext y; simp only [Set.mem_sdiff, mem_empty_iff_false, iff_false]
          exact fun h => h.2 h.1.1
        rw [this, measure_empty]
    rw [setLIntegral_congr hae]
    have hn12 : (1 / 2 : ℝ) ≤ (nd X : ℝ) := by
      have : (2 : ℝ) ≤ nd X := by exact_mod_cast hn2
      linarith
    calc ∫⁻ y in U', ENNReal.ofReal (densF X x0 y) *
          (ENNReal.ofReal (‖Hx α y‖ ^ 2 / kaF X x0 bb y) * weightFunctionOnFrames X Xa (cpt X x0 y))
        ≤ ∫⁻ y in U', ENNReal.ofReal (Cs ^ ((nd X : ℝ) - 1 / 2) * Cw ^ (1 / 2 : ℝ)) *
            ENNReal.ofReal (‖H α y‖ ^ 2 * Ss X Xa Fl x0 y ^ (-((nd X : ℝ) - 1 / 2)) *
              Real.exp (-ph0 X Xa x0 bb y)) := by
          refine setLIntegral_mono' hU'o.measurableSet fun y hy => ?_
          rw [hHxeq α hα hy]
          exact weightedDensity_bound X Xa Fl x0 bb hy.1 (hSs y hy) (H α) (hCs _ hy.1) (hCw _ hy.1) hn12
      _ < ⊤ := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
          have := (hH α hα).2
          rw [hexp] at this
          exact this
  · have hcont : ContinuousOn (fun z => F z - ∑ α ∈ Finset.Nat.antidiagonalTuple (nd X) (Xa.T - nd X),
        (∏ k, Fl.s k (cpt X x0 z) ^ α k) * Hx α z) (OmF X x0) := by
      refine hF.continuousOn.sub (continuousOn_finsetSum _ fun α hα => ?_)
      exact (continuousOn_finsetProd _ fun k _ => ((hsvO k).continuousOn.pow _)).mul
        (hHxd α hα).continuousOn
    have h0 := UpDivF.eq_across hU hUc hg1 hg10 hcont (fun y hy hgy => by
      have hy' : y ∈ U' := ⟨hy, hgy⟩
      rw [hid y hy', sub_eq_zero]
      refine Finset.sum_congr rfl fun α hα => ?_
      rw [hHxeq α hα hy']) z hz
    exact sub_eq_zero.mp h0

end ReciprocityTheory.ChartRestriction.G.AR.Up
