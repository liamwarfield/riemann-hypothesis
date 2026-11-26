module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedPowerSeriesEvaluationDivisibility
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeyValueTwoFibresLocalRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpreadMorphismBasicOpenAgreeFlat

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsForallNeZeroOfCountableAnalytic
open scoped BigOperators
open Matrix

namespace GlobalTheory

theorem exists_forall_ne_zero_of_countable_analytic :
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (U : Set E),
      IsOpen U → IsPreconnected U → U.Nonempty → ∀ (ι : Type) [Countable ι] (f : ι → E → ℂ),
      (∀ i, AnalyticOnNhd ℂ (f i) U) → (∀ i, ∃ x ∈ U, f i x ≠ 0) →
      ∃ x ∈ U, ∀ i, f i x ≠ 0 := by
  intro E _ _ _ U hU hc hne ι _ f hf hnz
  let S : ι → Set E := fun i => (U ∩ f i ⁻¹' ({0}ᶜ)) ∪ (closure U)ᶜ
  have hopen : ∀ i, IsOpen (S i) := fun i =>
    ((hf i).continuousOn.isOpen_inter_preimage hU isOpen_compl_singleton).union
      isClosed_closure.isOpen_compl
  have hdense : ∀ i, Dense (S i) := by
    intro i
    rw [dense_iff_inter_open]
    intro V hV hVne
    by_cases hVU : (V ∩ U).Nonempty
    · obtain ⟨z, hzV, hzU⟩ := hVU
      by_contra hcon
      have hzero : ∀ y ∈ V ∩ U, f i y = 0 := by
        intro y hy
        by_contra hy0
        exact hcon ⟨y, hy.1, Or.inl ⟨hy.2, hy0⟩⟩
      have hev : f i =ᶠ[nhds z] 0 := by
        filter_upwards [(hV.inter hU).mem_nhds ⟨hzV, hzU⟩] with y hy
        exact hzero y hy
      have hall := (hf i).eqOn_zero_of_preconnected_of_eventuallyEq_zero hc hzU hev
      obtain ⟨x, hxU, hx⟩ := hnz i
      exact hx (hall hxU)
    · obtain ⟨z, hzV⟩ := hVne
      refine ⟨z, hzV, Or.inr ?_⟩
      intro hz
      exact hVU (mem_closure_iff.1 hz V hV hzV)
  have hD : Dense (⋂ i, S i) := dense_iInter_of_isOpen hopen hdense
  obtain ⟨x, hxU, hx⟩ := hD.inter_open_nonempty U hU hne
  refine ⟨x, hxU, fun i => ?_⟩
  rcases Set.mem_iInter.1 hx i with h | h
  · exact h.2
  · exact absurd (subset_closure hxU) h

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDeformationBaseRingLocalDomain
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedPowerSeriesEvaluationDivisibilityStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bounded_power_series_evaluation_divisibility : ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] (π : C), ‖π‖ < 1 → ∃ (B : Subring (PowerSeries C)) (ev : B →+* C) (t : B), (∀ Φ, Φ ∈ B ↔ ∃ b : ℝ, ∀ n, ‖PowerSeries.coeff n Φ‖ ≤ b) ∧ (∀ Φ : B, ev Φ = ∑' n, PowerSeries.coeff n (Φ : PowerSeries C) * π ^ n) ∧ t ≠ 0 ∧ (∀ Φ, ev Φ = 0 ↔ t ∣ Φ) ∧ ∀ Φ : B, Φ ≠ 0 → ∃ n : ℕ, ¬ t ^ n ∣ Φ := by
  first | exact @GlobalTheory.MBLow.BddPS.main | exact GlobalTheory.MBLow.BddPS.main | (intros; apply GlobalTheory.MBLow.BddPS.main <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPuncturedDiscInjectiveEvalAtPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPuncturedDiscInjectiveEvalAtPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PowEval

noncomputable def absConv (u : ℂ) : Subring (PowerSeries ℂ) where
  carrier := {Φ | Summable fun n => ‖PowerSeries.coeff n Φ * u ^ n‖}
  zero_mem' := by simp
  one_mem' := by
    refine summable_of_ne_finset_zero (s := {0}) fun n hn => ?_
    simp [PowerSeries.coeff_one, Finset.notMem_singleton.1 hn]
  add_mem' := by
    intro f g hf hg
    refine (Summable.add hf hg).of_nonneg_of_le (fun _ => norm_nonneg _) fun n => ?_
    rw [map_add (f := _), add_mul]
    exact norm_add_le _ _
  neg_mem' := by
    intro f hf
    simpa [map_neg, neg_mul, norm_neg] using hf
  mul_mem' := by
    intro f g hf hg
    have e : ∀ n, PowerSeries.coeff n (f * g) * u ^ n = ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
        (PowerSeries.coeff kl.1 f * u ^ kl.1) * (PowerSeries.coeff kl.2 g * u ^ kl.2) := fun n => by
      rw [PowerSeries.coeff_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun kl h => ?_
      rw [← Finset.HasAntidiagonal.mem_antidiagonal.1 h, pow_add]
      ring
    show Summable fun n => ‖PowerSeries.coeff n (f * g) * u ^ n‖
    simp only [e]
    exact summable_norm_sum_mul_antidiagonal_of_summable_norm
      (f := fun n => PowerSeries.coeff n f * u ^ n) (g := fun n => PowerSeries.coeff n g * u ^ n) hf hg

noncomputable def evalAt (u : ℂ) : absConv u →+* ℂ where
  toFun Φ := ∑' n, PowerSeries.coeff n (Φ : PowerSeries ℂ) * u ^ n
  map_one' := by
    rw [tsum_eq_single 0 fun n hn => by simp [PowerSeries.coeff_one, hn]]
    simp
  map_zero' := by simp
  map_add' := by
    intro f g
    have hf : Summable fun n => ‖PowerSeries.coeff n (f : PowerSeries ℂ) * u ^ n‖ := f.2
    have hg : Summable fun n => ‖PowerSeries.coeff n (g : PowerSeries ℂ) * u ^ n‖ := g.2
    simp only [Subring.coe_add, map_add (f := _), add_mul]
    exact hf.of_norm.tsum_add hg.of_norm
  map_mul' := by
    intro f g
    have hf : Summable fun n => ‖PowerSeries.coeff n (f : PowerSeries ℂ) * u ^ n‖ := f.2
    have hg : Summable fun n => ‖PowerSeries.coeff n (g : PowerSeries ℂ) * u ^ n‖ := g.2
    rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf hg]
    refine tsum_congr fun n => ?_
    simp only [Subring.coe_mul]
    rw [PowerSeries.coeff_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun kl h => ?_
    rw [← Finset.HasAntidiagonal.mem_antidiagonal.1 h, pow_add]
    ring

theorem countable_closure {A : Type} [CommRing A] (S : Set A) (hS : S.Countable) :
    Countable (Subring.closure S) := by
  have : Countable S := hS.to_subtype
  have : Countable (MvPolynomial S ℤ) :=
    (MvPolynomial.basisMonomials S ℤ).repr.injective.countable
  let φ : MvPolynomial S ℤ →+* A := MvPolynomial.eval₂Hom (Int.castRingHom A) Subtype.val
  have hle : Subring.closure S ≤ φ.range := Subring.closure_le.2 fun s hs =>
    ⟨MvPolynomial.X ⟨s, hs⟩, by simp [φ]⟩
  have hc : (φ.range : Set A).Countable := by
    rw [RingHom.coe_range]; exact Set.countable_range _
  exact (hc.mono hle).to_subtype

theorem radius_ge (ε : ℝ) (Φ : PowerSeries ℂ)
    (h : ∀ u : ℂ, u ≠ 0 → ‖u‖ < ε → Summable fun n => ‖PowerSeries.coeff n Φ * u ^ n‖) :
    ENNReal.ofReal ε ≤ (FormalMultilinearSeries.ofScalars ℂ fun n => PowerSeries.coeff n Φ).radius := by
  refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
  by_cases hr0 : r = 0
  · simp [hr0]
  have hrε : (r : ℝ) < ε := by
    rw [← ENNReal.ofReal_coe_nnreal] at hr
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg r.2).1 hr
  refine FormalMultilinearSeries.le_radius_of_summable _ ?_
  have hs := h (r : ℂ) (by exact_mod_cast hr0) (by simpa using hrε)
  refine hs.congr fun n => ?_
  rw [FormalMultilinearSeries.ofScalars_norm, norm_mul, norm_pow]
  simp

end GlobalTheory.PowEval


open GlobalTheory.PowEval in
theorem GlobalTheory.exists_injective_evalAt_closure : ∀ (ε : ℝ) (S : Set (PowerSeries ℂ)), 0 < ε → S.Countable → (∀ Φ ∈ S, ∀ u : ℂ, u ≠ 0 → ‖u‖ < ε → Summable fun n => ‖PowerSeries.coeff n Φ * u ^ n‖) → ∃ (u : ℂ) (i : Subring.closure S →+* ℂ), u ≠ 0 ∧ ‖u‖ < ε ∧ Function.Injective i ∧ ∀ Φ : Subring.closure S, i Φ = ∑' n, PowerSeries.coeff n (Φ : PowerSeries ℂ) * u ^ n := by
  intro ε S hε hS h
  have : Countable (Subring.closure S) := countable_closure S hS
  let p : PowerSeries ℂ → FormalMultilinearSeries ℂ ℂ ℂ := fun Φ =>
    FormalMultilinearSeries.ofScalars ℂ fun n => PowerSeries.coeff n Φ
  have hsum : ∀ (Φ : PowerSeries ℂ) (u : ℂ), (p Φ).sum u = ∑' n, PowerSeries.coeff n Φ * u ^ n := by
    intro Φ u
    show FormalMultilinearSeries.ofScalarsSum _ u = _
    rw [FormalMultilinearSeries.ofScalars_sum_eq]
    simp [smul_eq_mul]
  have hcl : ∀ Φ ∈ Subring.closure S, ∀ u : ℂ, u ≠ 0 → ‖u‖ < ε →
      Summable fun n => ‖PowerSeries.coeff n Φ * u ^ n‖ := by
    intro Φ hΦ u hu0 hu
    have hle : Subring.closure S ≤ absConv u := Subring.closure_le.2 fun Ψ hΨ => h Ψ hΨ u hu0 hu
    exact hle hΦ
  have hrad : ∀ Φ ∈ Subring.closure S, ENNReal.ofReal ε ≤ (p Φ).radius := fun Φ hΦ =>
    radius_ge ε Φ (hcl Φ hΦ)
  have hpos : ∀ Φ ∈ Subring.closure S, 0 < (p Φ).radius := fun Φ hΦ =>
    lt_of_lt_of_le (ENNReal.ofReal_pos.2 hε) (hrad Φ hΦ)
  have hball : ∀ Φ ∈ Subring.closure S, Metric.ball (0 : ℂ) ε ⊆ Metric.eball 0 (p Φ).radius := by
    intro Φ hΦ
    rw [← Metric.eball_ofReal]
    exact Metric.eball_subset_eball (hrad Φ hΦ)
  let J := Option {Φ : Subring.closure S // Φ ≠ 0}
  let f : J → ℂ → ℂ := fun i => match i with
    | none => id
    | some Φ => (p (Φ.1 : PowerSeries ℂ)).sum
  have han : ∀ i, AnalyticOnNhd ℂ (f i) (Metric.ball 0 ε) := by
    intro i
    cases i with
    | none => exact analyticOnNhd_id
    | some Φ =>
      exact ((p _).hasFPowerSeriesOnBall (hpos _ Φ.1.2)).analyticOnNhd.mono (hball _ Φ.1.2)
  have hnz : ∀ i, ∃ x ∈ Metric.ball (0 : ℂ) ε, f i x ≠ 0 := by
    intro i
    cases i with
    | none =>
      refine ⟨((ε / 2 : ℝ) : ℂ), ?_, ?_⟩
      · rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
        linarith
      · show ((ε / 2 : ℝ) : ℂ) ≠ 0
        exact_mod_cast (by linarith : ε / 2 ≠ 0)
    | some Φ =>
      by_contra hcon
      push Not at hcon
      have hev : (p (Φ.1 : PowerSeries ℂ)).sum =ᶠ[nhds 0] 0 := by
        filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hε] with y hy
        exact hcon y hy
      have h0 := ((p _).hasFPowerSeriesOnBall (hpos _ Φ.1.2)).hasFPowerSeriesAt.eq_zero_of_eventually hev
      apply Φ.2
      apply Subtype.ext
      ext n
      have := congrArg (fun q : FormalMultilinearSeries ℂ ℂ ℂ => q n) h0
      simpa using (FormalMultilinearSeries.ofScalars_eq_zero (E := ℂ) (c := fun n => PowerSeries.coeff n (Φ.1 : PowerSeries ℂ)) n).1 this
  obtain ⟨u, hu, hx⟩ := GlobalTheory.exists_forall_ne_zero_of_countable_analytic ℂ (Metric.ball 0 ε)
    Metric.isOpen_ball (convex_ball 0 ε).isPreconnected (Metric.nonempty_ball.2 hε) J f han hnz
  have hu0 : u ≠ 0 := hx none
  have hun : ‖u‖ < ε := mem_ball_zero_iff.1 hu
  have hle : Subring.closure S ≤ absConv u := Subring.closure_le.2 fun Ψ hΨ => h Ψ hΨ u hu0 hun
  let i : Subring.closure S →+* ℂ := (evalAt u).comp (Subring.inclusion hle)
  refine ⟨u, i, hu0, hun, ?_, fun Φ => rfl⟩
  refine (injective_iff_map_eq_zero i).2 fun Φ hΦ => ?_
  by_contra hne
  apply hx (some ⟨Φ, hne⟩)
  show (p (Φ : PowerSeries ℂ)).sum u = 0
  rw [hsum]
  exact hΦ
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPuncturedDiscInjectiveEvalAtPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_puncturedDisc_injective_evalAtPoint : ∀ (ε : ℝ) (S : Set (PowerSeries ℂ)), 0 < ε → S.Countable → (∀ Φ ∈ S, ∀ u : ℂ, u ≠ 0 → ‖u‖ < ε → Summable fun n => ‖PowerSeries.coeff n Φ * u ^ n‖) → ∃ (u : ℂ) (i : Subring.closure S →+* ℂ), u ≠ 0 ∧ ‖u‖ < ε ∧ Function.Injective i ∧ ∀ Φ : Subring.closure S, i Φ = ∑' n, PowerSeries.coeff n (Φ : PowerSeries ℂ) * u ^ n := by
  first | exact @GlobalTheory.exists_injective_evalAt_closure | exact GlobalTheory.exists_injective_evalAt_closure | (intros; apply GlobalTheory.exists_injective_evalAt_closure <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNoetherianLocalOfOrderFunction
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNoetherianLocalOfOrderFunction
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MBLow.OrdRing

section General

variable (R : Type) [CommRing R] [IsDomain R] [ValuationRing R]

noncomputable def intRing : ValuationSubring (FractionRing R) :=
  { (algebraMap R (FractionRing R)).range with
    mem_or_inv_mem' := fun x => by
      rcases ValuationRing.isInteger_or_isInteger R x with ⟨y, hy⟩ | ⟨y, hy⟩
      · exact Or.inl ⟨y, hy⟩
      · exact Or.inr ⟨y, hy⟩ }

noncomputable def intEquiv : R ≃+* intRing R :=
  RingEquiv.ofBijective ((algebraMap R (FractionRing R)).codRestrict (intRing R) fun y => ⟨y, rfl⟩)
    ⟨fun a b h => IsFractionRing.injective R (FractionRing R) (congrArg Subtype.val h),
     fun ⟨x, ⟨y, hy⟩⟩ => ⟨y, Subtype.ext hy⟩⟩

variable {K : Type} [Field K] (φ : K →+* FractionRing R)

noncomputable def res : (intRing R).comap φ →+* R :=
  (intEquiv R).symm.toRingHom.comp (φ.restrict ((intRing R).comap φ) (intRing R) fun _ h => h)

theorem algebraMap_res (w : (intRing R).comap φ) :
    algebraMap R (FractionRing R) (res R φ w) = φ w :=
  congrArg Subtype.val ((intEquiv R).apply_symm_apply _)

theorem res_injective : Function.Injective (res R φ) := by
  intro a b h
  have := congrArg (algebraMap R (FractionRing R)) h
  rw [algebraMap_res, algebraMap_res] at this
  exact Subtype.ext (φ.injective this)

theorem dvd_of_res_dvd {x y : (intRing R).comap φ} (hy : y ≠ 0) (h : res R φ y ∣ res R φ x) :
    y ∣ x := by
  obtain ⟨c, hc⟩ := h
  have hyK : (y : K) ≠ 0 := fun h0 => hy (Subtype.ext h0)
  have hy' : algebraMap R (FractionRing R) (res R φ y) ≠ 0 := by
    rw [algebraMap_res]; exact (map_ne_zero φ).2 hyK
  have hmem : (x : K) / y ∈ (intRing R).comap φ := by
    rw [ValuationSubring.mem_comap, map_div₀, ← algebraMap_res, ← algebraMap_res, hc, map_mul,
      mul_div_cancel_left₀ _ hy']
    exact ⟨c, rfl⟩
  refine ⟨⟨_, hmem⟩, Subtype.ext ?_⟩
  show (x : K) = (y : K) * ((x : K) / y)
  field_simp

theorem isUnit_of_isUnit_res {a : (intRing R).comap φ} (h : IsUnit (res R φ a)) : IsUnit a := by
  have ha : a ≠ 0 := by rintro rfl; rw [map_zero] at h; exact not_isUnit_zero h
  refine isUnit_of_dvd_one (dvd_of_res_dvd R φ ha ?_)
  rw [map_one]; exact h.dvd

variable [IsDiscreteValuationRing R]

theorem isPrincipalIdealRing_comap : IsPrincipalIdealRing ((intRing R).comap φ) := by
  refine ⟨fun I => ?_⟩
  by_cases hI : I = ⊥
  · subst hI; exact bot_isPrincipal
  obtain ⟨y0, hy0, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  let s : Set ((intRing R).comap φ) := {x | x ∈ I ∧ x ≠ 0}
  have hs : s.Nonempty := ⟨y0, hy0, hne⟩
  let y := Function.argminOn (fun x => IsDiscreteValuationRing.addVal R (res R φ x)) s hs
  have hy : y ∈ s := Function.argminOn_mem _ _ hs
  refine ⟨⟨y, le_antisymm ?_ ?_⟩⟩
  · intro x hx
    by_cases hx0 : x = 0
    · subst hx0; exact Submodule.zero_mem _
    rw [Ideal.submodule_span_eq, Ideal.mem_span_singleton]
    exact dvd_of_res_dvd R φ hy.2
      (IsDiscreteValuationRing.addVal_le_iff_dvd.1 (Function.argminOn_le (fun x => IsDiscreteValuationRing.addVal R (res R φ x)) s ⟨hx, hx0⟩))
  · rw [Submodule.span_le, Set.singleton_subset_iff]; exact hy.1

theorem mem_of_prime {q : Ideal ((intRing R).comap φ)} (hq : q.IsPrime) (hq0 : q ≠ ⊥)
    (a : (intRing R).comap φ) : a ∈ q ↔ ¬ IsUnit (res R φ a) := by
  constructor
  · intro ha hu
    exact hq.ne_top (Ideal.eq_top_of_isUnit_mem q ha (isUnit_of_isUnit_res R φ hu))
  · intro hna
    obtain ⟨y, hyq, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hq0
    have hry : res R φ y ≠ 0 := fun h => hy0 (res_injective R φ (by rw [h, map_zero]))
    have hfin : IsDiscreteValuationRing.addVal R (res R φ y) ≠ ⊤ :=
      fun h => hry (IsDiscreteValuationRing.addVal_eq_top_iff.1 h)
    set N := (IsDiscreteValuationRing.addVal R (res R φ y)).toNat with hN
    have h1 : 1 ≤ IsDiscreteValuationRing.addVal R (res R φ a) :=
      ENat.one_le_iff_ne_zero.2 fun h => hna (IsDiscreteValuationRing.addVal_eq_zero_iff.1 h)
    have hle : IsDiscreteValuationRing.addVal R (res R φ y) ≤
        IsDiscreteValuationRing.addVal R (res R φ (a ^ N)) := by
      rw [map_pow, IsDiscreteValuationRing.addVal_pow, ← ENat.coe_toNat hfin, ← hN]
      calc (N : ℕ∞) = N • (1 : ℕ∞) := by simp
        _ ≤ N • IsDiscreteValuationRing.addVal R (res R φ a) := nsmul_le_nsmul_right h1 N
    have hd := dvd_of_res_dvd R φ hy0 (IsDiscreteValuationRing.addVal_le_iff_dvd.1 hle)
    exact hq.mem_of_pow_mem N (Ideal.mem_of_dvd _ hd hyq)

end General

end GlobalTheory.MBLow.OrdRing

namespace GlobalTheory.MBLow.OrdRing

section Order

variable {B C : Type} [CommRing B] [IsDomain B] [Field C] (ev : B →+* C) (t : B)

theorem exists_pow_mul_not_dvd (hfin : ∀ b : B, b ≠ 0 → ∃ n : ℕ, ¬ t ^ n ∣ b) {b : B}
    (hb : b ≠ 0) : ∃ (n : ℕ) (c : B), b = t ^ n * c ∧ ¬ t ∣ c := by
  obtain ⟨n, hn⟩ := hfin b hb
  have hf : FiniteMultiplicity t b := ⟨n, fun h => hn ((pow_dvd_pow t (Nat.le_succ n)).trans h)⟩
  obtain ⟨c, hc, hnd⟩ := hf.exists_eq_pow_mul_and_not_dvd
  exact ⟨_, c, hc, hnd⟩

theorem ker_eq_span (hker : ∀ b, ev b = 0 ↔ t ∣ b) : RingHom.ker ev = Ideal.span {t} := by
  ext b; rw [RingHom.mem_ker, Ideal.mem_span_singleton, hker]

theorem map_ker_eq_span (hker : ∀ b, ev b = 0 ↔ t ∣ b) :
    IsLocalRing.maximalIdeal (Localization.AtPrime (RingHom.ker ev)) =
      Ideal.span {algebraMap B (Localization.AtPrime (RingHom.ker ev)) t} := by
  have h := congrArg (Ideal.map (algebraMap B (Localization.AtPrime (RingHom.ker ev))))
    (ker_eq_span ev t hker)
  rw [Ideal.map_span, Set.image_singleton] at h
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (RingHom.ker ev)]
  exact h

theorem isDVR (ht : t ≠ 0) (hker : ∀ b, ev b = 0 ↔ t ∣ b)
    (hfin : ∀ b : B, b ≠ 0 → ∃ n : ℕ, ¬ t ^ n ∣ b) :
    IsDiscreteValuationRing (Localization.AtPrime (RingHom.ker ev)) := by
  set P := RingHom.ker ev
  have hinj : Function.Injective (algebraMap B (Localization.AtPrime P)) :=
    IsLocalization.injective _ P.primeCompl_le_nonZeroDivisors
  have ht' : algebraMap B (Localization.AtPrime P) t ≠ 0 :=
    fun h => ht (hinj (by rw [h, map_zero]))
  have htprime : Prime (algebraMap B (Localization.AtPrime P) t) := by
    rw [← Ideal.span_singleton_prime ht', ← map_ker_eq_span ev t hker]
    infer_instance
  refine IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨_, htprime.irreducible, fun {x} hx => ?_⟩
  obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl x
  have hb : b ≠ 0 := by rintro rfl; exact hx (IsLocalization.mk'_zero _)
  obtain ⟨n, c, rfl, hc⟩ := exists_pow_mul_not_dvd t hfin hb
  have hcP : c ∈ P.primeCompl := fun h => hc ((hker c).1 (RingHom.mem_ker.1 h))
  have hu := IsLocalization.map_units (Localization.AtPrime P) (⟨c, hcP⟩ : P.primeCompl)
  have hs := IsLocalization.map_units (Localization.AtPrime P) s
  refine ⟨n, hu.unit * hs.unit⁻¹, ?_⟩
  rw [eq_comm, IsLocalization.mk'_eq_iff_eq_mul, Units.val_mul, IsUnit.unit_spec, map_mul, map_pow,
    _root_.mul_assoc, _root_.mul_assoc, hs.val_inv_mul, _root_.mul_one]

noncomputable def evLoc : Localization.AtPrime (RingHom.ker ev) →+* C :=
  IsLocalization.lift (M := (RingHom.ker ev).primeCompl) (g := ev)
    fun y => isUnit_iff_ne_zero.2 fun h => y.2 (RingHom.mem_ker.2 h)

theorem evLoc_algebraMap (b : B) :
    evLoc ev (algebraMap B (Localization.AtPrime (RingHom.ker ev)) b) = ev b :=
  IsLocalization.lift_eq _ _

theorem evLoc_eq_zero_iff (hker : ∀ b, ev b = 0 ↔ t ∣ b)
    (z : Localization.AtPrime (RingHom.ker ev)) : evLoc ev z = 0 ↔ ¬ IsUnit z := by
  constructor
  · intro h hu; exact (hu.map (evLoc ev)).ne_zero h
  · intro hz
    have hm : z ∈ IsLocalRing.maximalIdeal _ := hz
    rw [map_ker_eq_span ev t hker, Ideal.mem_span_singleton] at hm
    obtain ⟨c, rfl⟩ := hm
    rw [map_mul, evLoc_algebraMap, (hker t).2 dvd_rfl, zero_mul]

end Order

end GlobalTheory.MBLow.OrdRing

namespace GlobalTheory.MBLow.OrdRing

theorem exists_of_dvr (A B C Ω : Type) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [Field C] [Field Ω] (f : A →+* B) (ev : B →+* C) (i : A →+* Ω)
    (hf : Function.Injective f) (hi : Function.Injective i)
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (j : B →+* R)
    (hj : Function.Injective j) (ev' : R →+* C) (hev : ∀ b, ev' (j b) = ev b)
    (hzero : ∀ z, ev' z = 0 ↔ ¬ IsUnit z) :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsNoetherianRing W) (_ : IsLocalRing W)
      (_ : IsIntegrallyClosed W) (g : A →+* W) (i₀ : W →+* Ω) (i₁ : W →+* C),
      Function.Injective i₀ ∧ i₀.comp g = i ∧ i₁.comp g = ev.comp f ∧
      (∀ a, i₁ a ≠ 0 → IsUnit a) ∧
      ∀ q : Ideal W, q.IsPrime → q = RingHom.ker i₀ ∨ q = RingHom.ker i₁ := by
  have hg : Function.Injective ((algebraMap R (FractionRing R)).comp (j.comp f)) :=
    (IsFractionRing.injective R (FractionRing R)).comp (hj.comp hf)
  let φ : FractionRing A →+* FractionRing R := IsFractionRing.lift hg
  let V := (intRing R).comap φ
  haveI : IsPrincipalIdealRing V := isPrincipalIdealRing_comap R φ
  have hmemA : ∀ a : A, algebraMap A (FractionRing A) a ∈ V := fun a => by
    rw [ValuationSubring.mem_comap, IsFractionRing.lift_algebraMap]
    exact ⟨j (f a), rfl⟩
  let g : A →+* V := (algebraMap A (FractionRing A)).codRestrict V hmemA
  let i₀ : V →+* Ω := (IsFractionRing.lift hi).comp V.subtype
  have hi₀ : Function.Injective i₀ := fun x y h => Subtype.ext ((IsFractionRing.lift hi).injective h)
  have hres : ∀ a : A, res R φ (g a) = j (f a) := fun a => by
    apply IsFractionRing.injective R (FractionRing R)
    rw [algebraMap_res]
    exact IsFractionRing.lift_algebraMap hg a
  refine ⟨V, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, g, i₀,
    ev'.comp (res R φ), hi₀, ?_, ?_, ?_, ?_⟩
  · ext a
    exact IsFractionRing.lift_algebraMap hi a
  · ext a
    simp only [RingHom.comp_apply]
    rw [hres, hev]
  · intro a ha
    exact isUnit_of_isUnit_res R φ (not_not.1 fun h => ha ((hzero _).2 h))
  · intro q hq
    by_cases hq0 : q = ⊥
    · left; rw [hq0, (RingHom.injective_iff_ker_eq_bot _).1 hi₀]
    · right
      ext a
      rw [mem_of_prime R φ hq hq0, RingHom.mem_ker, RingHom.comp_apply, hzero]

end GlobalTheory.MBLow.OrdRing

namespace GlobalTheory.MBLow


open GlobalTheory.MBLow.OrdRing in
theorem exists_localRing_of_order : ∀ (A B C Ω : Type) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Field C] [Field Ω] (f : A →+* B) (ev : B →+* C) (t : B) (i : A →+* Ω), Function.Injective f → Function.Injective i → t ≠ 0 → (∀ b, ev b = 0 ↔ t ∣ b) → (∀ b : B, b ≠ 0 → ∃ n : ℕ, ¬ t ^ n ∣ b) → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsNoetherianRing W) (_ : IsLocalRing W) (_ : IsIntegrallyClosed W) (g : A →+* W) (i₀ : W →+* Ω) (i₁ : W →+* C), Function.Injective i₀ ∧ i₀.comp g = i ∧ i₁.comp g = ev.comp f ∧ (∀ a, i₁ a ≠ 0 → IsUnit a) ∧ ∀ q : Ideal W, q.IsPrime → q = RingHom.ker i₀ ∨ q = RingHom.ker i₁ := by
  intro A B C Ω _ _ _ _ _ _ f ev t i hf hi ht hker hfin
  haveI := isDVR ev t ht hker hfin
  exact exists_of_dvr A B C Ω f ev i hf hi (Localization.AtPrime (RingHom.ker ev))
    (algebraMap B _) (IsLocalization.injective _ (RingHom.ker ev).primeCompl_le_nonZeroDivisors)
    (evLoc ev) (evLoc_algebraMap ev) (evLoc_eq_zero_iff ev t hker)

end GlobalTheory.MBLow
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNoetherianLocalOfOrderFunctionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_noetherianLocal_of_orderFunction : ∀ (A B C Ω : Type) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Field C] [Field Ω] (f : A →+* B) (ev : B →+* C) (t : B) (i : A →+* Ω), Function.Injective f → Function.Injective i → t ≠ 0 → (∀ b, ev b = 0 ↔ t ∣ b) → (∀ b : B, b ≠ 0 → ∃ n : ℕ, ¬ t ^ n ∣ b) → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsNoetherianRing W) (_ : IsLocalRing W) (_ : IsIntegrallyClosed W) (g : A →+* W) (i₀ : W →+* Ω) (i₁ : W →+* C), Function.Injective i₀ ∧ i₀.comp g = i ∧ i₁.comp g = ev.comp f ∧ (∀ a, i₁ a ≠ 0 → IsUnit a) ∧ ∀ q : Ideal W, q.IsPrime → q = RingHom.ker i₀ ∨ q = RingHom.ker i₁ := by
  first | exact @GlobalTheory.MBLow.exists_localRing_of_order | exact GlobalTheory.MBLow.exists_localRing_of_order | (intros; apply GlobalTheory.MBLow.exists_localRing_of_order <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDeformationBaseRingLocalDomain
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MBLow

theorem tsum_coeff_C_mul_pow_eq {K : Type} [NormedField K] (a u : K) :
    ∑' n, PowerSeries.coeff n (PowerSeries.C a) * u ^ n = a := by
  rw [tsum_eq_single 0 (fun n hn => by simp [PowerSeries.coeff_C, hn])]
  simp

theorem summable_coeff_C_mul_pow {K : Type} [NormedField K] (a u : K) :
    Summable fun n => ‖PowerSeries.coeff n (PowerSeries.C a) * u ^ n‖ :=
  (hasSum_single 0 (fun n hn => by simp [PowerSeries.coeff_C, hn])).summable

theorem ring_of_deformation : ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [CharZero C] (e : C →+* ℂ) (I I' : Type) [Finite I] [Finite I'] (Φ : I → PowerSeries C) (c : I' → C) (π : C) (b ε : ℝ), ‖π‖ < 1 → 0 < ε → (∀ a n, ‖PowerSeries.coeff n (Φ a)‖ ≤ b) → (∀ u : ℂ, u ≠ 0 → ‖u‖ < ε → ∀ a, Summable fun n => ‖e (PowerSeries.coeff n (Φ a)) * u ^ n‖) → ∃ (u : ℂ) (o : Type) (_ : Field o) (_ : CharZero o) (j : o →+* C) (c₀ : I' → o), u ≠ 0 ∧ ‖u‖ < ε ∧ (∀ a, j (c₀ a) = c a) ∧ ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsNoetherianRing W) (_ : IsLocalRing W) (_ : IsIntegrallyClosed W) (_ : CharZero W) (β : o →+* W) (i₀ : W →+* ℂ) (i₁ : W →+* C) (φ : I → W), Function.Injective i₀ ∧ i₀.comp β = e.comp j ∧ i₁.comp β = j ∧ (∀ a, i₁ a ≠ 0 → IsUnit a) ∧ (∀ q : Ideal W, q.IsPrime → q = RingHom.ker i₀ ∨ q = RingHom.ker i₁) ∧ ∀ a, i₀ (φ a) = ∑' n, e (PowerSeries.coeff n (Φ a)) * u ^ n ∧ i₁ (φ a) = ∑' n, PowerSeries.coeff n (Φ a) * π ^ n := by
  intro C _ _ _ _ e I I' _ _ Φ c π b ε hπ hε hb hsum
  classical

  set o : Subfield C := Subfield.closure (Set.range c) with ho_def
  have hoc : Countable o := by
    rw [← Cardinal.mk_le_aleph0_iff]
    exact (Subfield.cardinalMk_closure_le_max _).trans
      (max_le (Cardinal.mk_le_aleph0_iff.2 (Set.finite_range c).countable.to_subtype) le_rfl)

  set G : Set (PowerSeries C) :=
    Set.range (fun x : o => PowerSeries.C (x : C)) ∪ Set.range Φ with hG
  set A : Subring (PowerSeries C) := Subring.closure G with hA
  obtain ⟨B, ev, t, hB, hev, ht, hevt, hfin⟩ := GlobalTheory.T.bounded_power_series_evaluation_divisibility C π hπ
  have hAB : A ≤ B := by
    refine Subring.closure_le.2 ?_
    rintro _ (⟨x, rfl⟩ | ⟨a, rfl⟩)
    · refine (hB _).2 ⟨‖(x : C)‖, fun n => ?_⟩
      rw [PowerSeries.coeff_C]; split_ifs <;> simp
    · exact (hB _).2 ⟨b, hb a⟩

  set S : Set (PowerSeries ℂ) := PowerSeries.map e '' G with hS
  have hSc : S.Countable :=
    ((Set.countable_range _).union (Set.finite_range Φ).countable).image _
  have hSs : ∀ Ψ ∈ S, ∀ u : ℂ, u ≠ 0 → ‖u‖ < ε → Summable fun n => ‖PowerSeries.coeff n Ψ * u ^ n‖ := by
    rintro _ ⟨g, (⟨x, rfl⟩ | ⟨a, rfl⟩), rfl⟩ u hu0 hu
    · rw [PowerSeries.map_C]; exact summable_coeff_C_mul_pow _ _
    · simpa [PowerSeries.coeff_map] using hsum u hu0 hu a
  obtain ⟨u, ig, hu0, hu, hig, hige⟩ := GlobalTheory.T.exists_puncturedDisc_injective_evalAtPoint ε S hε hSc hSs
  have hmapA : ∀ x ∈ A, PowerSeries.map e x ∈ Subring.closure S := by
    intro x hx
    rw [hS, ← RingHom.map_closure]
    exact Subring.mem_map.2 ⟨x, hx, rfl⟩
  let m : A →+* Subring.closure S := (PowerSeries.map e).restrict A (Subring.closure S) hmapA
  have hm : ∀ x : A, (m x : PowerSeries ℂ) = PowerSeries.map e (x : PowerSeries C) := fun _ => rfl
  have hmapinj : Function.Injective (PowerSeries.map e) := by
    intro x y h
    ext n
    have := congrArg (PowerSeries.coeff n) h
    simp only [PowerSeries.coeff_map] at this
    exact e.injective this
  have hminj : Function.Injective m := by
    intro x y h
    apply Subtype.ext
    apply hmapinj
    rw [← hm, ← hm, h]
  let i : A →+* ℂ := ig.comp m
  have hi : Function.Injective i := hig.comp hminj
  let f : A →+* B := Subring.inclusion hAB
  have hf : Function.Injective f := fun x y h => Subtype.ext (congrArg Subtype.val h :)
  obtain ⟨W, _, _, _, _, _, g, i₀, i₁, hi₀, hgi₀, hgi₁, hunit, hprime⟩ :=
    GlobalTheory.T.exists_noetherianLocal_of_orderFunction A B C ℂ f ev t i hf hi ht hevt hfin
  let cA : o →+* A := (PowerSeries.C.comp o.subtype).codRestrict A
    (fun x => Subring.subset_closure (Or.inl ⟨x, rfl⟩))
  have hΦA : ∀ a, Φ a ∈ A := fun a => Subring.subset_closure (Or.inr ⟨a, rfl⟩)
  haveI : CharZero W := RingHom.charZero i₁
  refine ⟨u, o, inferInstance, inferInstance, o.subtype,
    fun a => ⟨c a, Subfield.subset_closure ⟨a, rfl⟩⟩, hu0, hu, fun a => rfl,
    W, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    g.comp cA, i₀, i₁, fun a => g ⟨Φ a, hΦA a⟩, hi₀, ?_, ?_, hunit, hprime, fun a => ⟨?_, ?_⟩⟩
  · ext x
    have h1 := RingHom.congr_fun hgi₀ (cA x)
    simp only [RingHom.comp_apply] at h1 ⊢
    rw [h1]
    show ig (m (cA x)) = e x
    rw [hige, hm]
    show ∑' n, PowerSeries.coeff n (PowerSeries.map e (PowerSeries.C (x : C))) * u ^ n = e x
    rw [PowerSeries.map_C, tsum_coeff_C_mul_pow_eq]
  · ext x
    have h1 := RingHom.congr_fun hgi₁ (cA x)
    simp only [RingHom.comp_apply] at h1 ⊢
    rw [h1, hev]
    show ∑' n, PowerSeries.coeff n (PowerSeries.C (x : C)) * π ^ n = x
    rw [tsum_coeff_C_mul_pow_eq]
  · have h1 := RingHom.congr_fun hgi₀ ⟨Φ a, hΦA a⟩
    simp only [RingHom.comp_apply] at h1
    rw [h1]
    show ig (m ⟨Φ a, hΦA a⟩) = _
    rw [hige, hm]
    simp only [PowerSeries.coeff_map]
  · have h1 := RingHom.congr_fun hgi₁ ⟨Φ a, hΦA a⟩
    simp only [RingHom.comp_apply] at h1
    rw [h1, hev]
    rfl

end GlobalTheory.MBLow
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDeformationBaseRingLocalDomainStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_deformation_base_ring_local_domain : ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [CharZero C] (e : C →+* ℂ) (I I' : Type) [Finite I] [Finite I'] (Φ : I → PowerSeries C) (c : I' → C) (π : C) (b ε : ℝ), ‖π‖ < 1 → 0 < ε → (∀ a n, ‖PowerSeries.coeff n (Φ a)‖ ≤ b) → (∀ u : ℂ, u ≠ 0 → ‖u‖ < ε → ∀ a, Summable fun n => ‖e (PowerSeries.coeff n (Φ a)) * u ^ n‖) → ∃ (u : ℂ) (o : Type) (_ : Field o) (_ : CharZero o) (j : o →+* C) (c₀ : I' → o), u ≠ 0 ∧ ‖u‖ < ε ∧ (∀ a, j (c₀ a) = c a) ∧ ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsNoetherianRing W) (_ : IsLocalRing W) (_ : IsIntegrallyClosed W) (_ : CharZero W) (β : o →+* W) (i₀ : W →+* ℂ) (i₁ : W →+* C) (φ : I → W), Function.Injective i₀ ∧ i₀.comp β = e.comp j ∧ i₁.comp β = j ∧ (∀ a, i₁ a ≠ 0 → IsUnit a) ∧ (∀ q : Ideal W, q.IsPrime → q = RingHom.ker i₀ ∨ q = RingHom.ker i₁) ∧ ∀ a, i₀ (φ a) = ∑' n, e (PowerSeries.coeff n (Φ a)) * u ^ n ∧ i₁ (φ a) = ∑' n, PowerSeries.coeff n (Φ a) * π ^ n := by
  first | exact @GlobalTheory.MBLow.ring_of_deformation | exact GlobalTheory.MBLow.ring_of_deformation | (intros; apply GlobalTheory.MBLow.ring_of_deformation <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFamilyLocalDomainOfTwoFibres
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFamilyLocalDomainOfTwoFibres
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MBLow.TwoFibres

open GlobalTheory.ZM

theorem unitS_spMap_eq {o R : Type} [CommRing o] [CommRing R] (β : o →+* R) (u : oˣ) :
    unitS (spMap β) u = unitOn (Units.map β.toMonoidHom u) := by
  apply Units.ext
  exact (congrArg (fun q => q.hom (u : o)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom β))).symm

theorem unitS_spMap_comp {o R R' : Type} [CommRing o] [CommRing R] [CommRing R'] (β : o →+* R) (i : R →+* R')
    (u : oˣ) : unitS (spMap i ≫ spMap β) u = unitOn (Units.map (i.comp β).toMonoidHom u) := by
  rw [SpreadLevel.unitS_comp, unitS_spMap_eq β]
  exact (unitS_spMap_eq i _).trans (congrArg unitOn (Units.ext rfl))

def ofLevel {o : Type} [CommRing o] {g k : ℕ} (hk : 0 < k) (b : TBase o k) {K : Type} [Field K] [IsAlgClosed K]
    (s : Sp K ⟶ Sp o) (P : PolAV (Sp K)) (hg : P.g = g) {ze : Γ(Sp K, ⊤)ˣ} (l : Level P k ze)
    (hze : ze = unitS s b.ζ) : TObj g k PEmpty b s where
  A := P.A
  ab := P.isAb
  dim := hg ▸ P.smoothDim
  L := P.L
  isLB := P.isLB
  rigid := P.rigid
  sym := P.sym
  ample := P.ample
  ktriv := P.ktriv
  pt := levelBasis l hg
  torsion := fun i => l.torsion _
  bij := by
    intro K' _ _ x y hy
    subst hg
    haveI : NeZero k := ⟨hk.ne'⟩
    obtain ⟨c, hc⟩ := l.span K' x y hy
    refine ⟨fun i => ((c i : ℕ) : ZMod k), ?_, fun c' hc' => ?_⟩
    · simp only [levelBasis_rfl, ZMod.val_natCast, Nat.mod_eq_of_lt (c _).2]
      exact hc
    · have e := l.indep K' x (fun i => ⟨(c' i).val, ZMod.val_lt _⟩) c (hc'.trans hc.symm)
      funext i
      have := congrArg (fun d => ((d i : ℕ) : ZMod k)) e
      simpa using this
  pairing := by
    intro i j
    subst hg hze
    exact l.pairing i j
  act := fun e => e.elim
  hom := fun e => e.elim

theorem ofLevel_lab {o : Type} [CommRing o] {g k : ℕ} (hk : 0 < k) (b : TBase o k) {K : Type} [Field K]
    [IsAlgClosed K] (s : Sp K ⟶ Sp o) (P : PolAV (Sp K)) (hg : P.g = g) {ze : Γ(Sp K, ⊤)ˣ} (l : Level P k ze)
    (hze : ze = unitS s b.ζ) (a : Ix g k) : (ofLevel hk b s P hg l hze).lab a = levelPoint l hg a := by
  subst hg
  rfl

theorem ofLevel_hasTh {o : Type} [CommRing o] {g k : ℕ} (hk : 0 < k ^ 2) (b : TBase o (k ^ 2)) {K : Type} [Field K]
    [IsAlgClosed K] (s : Sp K ⟶ Sp o) (P : PolAV (Sp K)) (hg : P.g = g) {ze : Γ(Sp K, ⊤)ˣ}
    (l : Level P (k ^ 2) ze) (hze : ze = unitS s b.ζ) (w : Ix g (k ^ 2) → K)
    (h : IsThetaPt P k (levelPoint l hg) fun a => Ex.fnOf (w a)) :
    (ofLevel hk b s P hg l hze).HasTh (𝟙 _) w := by
  have hx : (fun a => (Over.homMk (𝟙 (Sp K)) (by simp) : Over.mk (𝟙 (Sp K)) ⟶ Out.baseOver (Sp K)) ≫
      (ofLevel hk b s P hg l hze).lab a) = levelPoint l hg := by
    funext a
    have e : (Over.homMk (𝟙 (Sp K)) (by simp) : Over.mk (𝟙 (Sp K)) ⟶ Out.baseOver (Sp K)) = 𝟙 _ := by
      ext; rfl
    rw [e, Category.id_comp, ofLevel_lab]
  subst hg
  exact (congrArg (fun x => IsThetaPt P k x (fun a => Ex.fnOf (w a))) hx).mpr h

theorem linComb_push {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {m : ℕ} (x' : Fin m → (Out.baseOver S' ⟶ G'))
    (x : Fin m → (Out.baseOver S ⟶ G)) (hx : ∀ i, (x' i).left ≫ φ = f ≫ (x i).left) (c : Fin m → ℕ) :
    (Out.linComb x' c).left ≫ φ = f ≫ (Out.linComb x c).left := by
  let U : Over.mk ((Out.baseOver S').hom ≫ f) ⟶ Out.baseOver S := Over.homMk f (by simp)
  have e : ∀ i, pushHom h (Out.baseOver S') (x' i) = preHom U (x i) := fun i =>
    Over.OverMorphism.ext (hx i)
  have := congrArg (fun z => z.left) ((SpreadLevel.map_linComb (pushHom h (Out.baseOver S')) x' c).trans
    ((congrArg (fun z => Out.linComb z c) (funext e)).trans (SpreadLevel.map_linComb (preHom U) x c).symm))
  exact this

end GlobalTheory.MBLow.TwoFibres

namespace GlobalTheory.MBLow

open GlobalTheory.ZM GlobalTheory.MBLow.TwoFibres

theorem exists_family_of_two_fibres : ∀ g n : ℕ, n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [Field o] [CharZero o] (ζ : oˣ) (W : Type) [CommRing W] [IsDomain W] [IsNoetherianRing W] [IsLocalRing W] (β : o →+* W) (v : (Fin (2 * g) → ZMod ((n ^ j) ^ 2)) → W) (K₀ K₁ : Type) [Field K₀] [IsAlgClosed K₀] [Field K₁] [IsAlgClosed K₁] (i₀ : W →+* K₀) (i₁ : W →+* K₁), (∀ q : Ideal W, q.IsPrime → q = RingHom.ker i₀ ∨ q = RingHom.ker i₁) → ∀ (P₀ : PolAV (Sp K₀)) (P₁ : PolAV (Sp K₁)) (h₀ : P₀.g = g) (h₁ : P₁.g = g) (l₀ : Out.Level P₀ ((n ^ j) ^ 2) (unitOn (Units.map (i₀.comp β).toMonoidHom ζ))) (l₁ : Out.Level P₁ ((n ^ j) ^ 2) (unitOn (Units.map (i₁.comp β).toMonoidHom ζ))), (IsThetaPt P₀ (n ^ j) (levelPoint l₀ h₀) fun a => fnOf (i₀ (v a))) → (IsThetaPt P₁ (n ^ j) (levelPoint l₁ h₁) fun a => fnOf (i₁ (v a))) → ∃ (P : PolAV (Sp W)) (pt : (Fin (2 * g) → ZMod ((n ^ j) ^ 2)) → (baseOver (Sp W) ⟶ P.A)) (φ₀ : P₀.A.left ⟶ P.A.left) (φ₁ : P₁.A.left ⟶ P.A.left), P.g = g ∧ (∀ a, pt a ^ ((n ^ j) ^ 2) = 1) ∧ IsGrpPullback P₀.A P.A (spMap i₀) φ₀ ∧ IsGrpPullback P₁.A P.A (spMap i₁) φ₁ ∧ LBIso P₀.L (P.L.pull φ₀) ∧ LBIso P₁.L (P.L.pull φ₁) ∧ (∀ a, (levelPoint l₀ h₀ a).left ≫ φ₀ = spMap i₀ ≫ (pt a).left) ∧ ∀ a, (levelPoint l₁ h₁ a).left ≫ φ₁ = spMap i₁ ≫ (pt a).left := by
  intro g n hn hodd
  obtain ⟨hL, hL2⟩ := abelianSchemeLaws_all
  obtain ⟨j₀, H⟩ := exists_tObj_of_veryDense hL hL2 g PEmpty (fun e => e.elim) 0 n hn hodd
  refine ⟨j₀, fun j hj o _ _ ζ W _ _ _ _ β v K₀ K₁ _ _ _ _ i₀ i₁ hW P₀ P₁ h₀ h₁ l₀ l₁ hT₀ hT₁ => ?_⟩
  have hk : 0 < (n ^ j) ^ 2 := pow_pos (pow_pos hn.pos _) _
  have hζ : IsPrimitiveRoot ζ ((n ^ j) ^ 2) := by
    refine IsPrimitiveRoot.of_map_of_injective (f := (Units.map (Scheme.ΓSpecIso (CommRingCat.of K₀)).inv.hom.toMonoidHom).comp
      (Units.map (i₀.comp β).toMonoidHom)) l₀.prim ?_
    exact (Units.map_injective (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K₀)).inv).1).comp
      (Units.map_injective (i₀.comp β).injective)
  let b : TBase o ((n ^ j) ^ 2) :=
    { ζ := ζ
      unit := (Nat.cast_ne_zero.2 hk.ne').isUnit
      prim := fun K _ β' => (IsPrimitiveRoot.coe_units_iff.2 hζ).map_of_injective β'.injective }
  let t₀ := ofLevel hk b (spMap i₀ ≫ spMap β) P₀ h₀ l₀ (unitS_spMap_comp β i₀ ζ).symm
  let t₁ := ofLevel hk b (spMap i₁ ≫ spMap β) P₁ h₁ l₁ (unitS_spMap_comp β i₁ ζ).symm
  have hS₀ : t₀.Shape (fun e => e.elim) 0 := fun e => e.elim
  have hS₁ : t₁.Shape (fun e => e.elim) 0 := fun e => e.elim
  have hh₀ : t₀.HasTh (𝟙 _) (fun a => i₀ (v a)) :=
    ofLevel_hasTh hk b _ P₀ h₀ l₀ (unitS_spMap_comp β i₀ ζ).symm _ hT₀
  have hh₁ : t₁.HasTh (𝟙 _) (fun a => i₁ (v a)) :=
    ofLevel_hasTh hk b _ P₁ h₁ l₁ (unitS_spMap_comp β i₁ ζ).symm _ hT₁
  have hvd : VeryDense (objPrimes b (fun e : PEmpty => e.elim) 0 β v) := by
    intro q f hq hf
    rcases hW q hq with rfl | rfl
    · exact ⟨_, ⟨K₀, inferInstance, inferInstance, i₀, t₀, rfl, hS₀, hh₀⟩, hq, le_rfl, hf⟩
    · exact ⟨_, ⟨K₁, inferInstance, inferInstance, i₁, t₁, rfl, hS₁, hh₁⟩, hq, le_rfl, hf⟩
  obtain ⟨t, -, ht⟩ := H j hj o b W β v hvd
  obtain ⟨φ₀, hp₀, hL₀, hpt₀, -⟩ := ht K₀ i₀ t₀ hS₀ hh₀
  obtain ⟨φ₁, hp₁, hL₁, hpt₁, -⟩ := ht K₁ i₁ t₁ hS₁ hh₁
  haveI := t.ab.comm
  refine ⟨t.pol, t.lab, φ₀, φ₁, rfl, fun a => DenseBasis.linComb_pow_eq_one t.pt t.torsion _, hp₀, hp₁, hL₀, hL₁,
    fun a => ?_, fun a => ?_⟩
  · rw [← ofLevel_lab hk b (spMap i₀ ≫ spMap β) P₀ h₀ l₀ (unitS_spMap_comp β i₀ ζ).symm a]
    exact linComb_push hp₀ t₀.pt t.pt hpt₀ _
  · rw [← ofLevel_lab hk b (spMap i₁ ≫ spMap β) P₁ h₁ l₁ (unitS_spMap_comp β i₁ ζ).symm a]
    exact linComb_push hp₁ t₁.pt t.pt hpt₁ _

end GlobalTheory.MBLow
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFamilyLocalDomainOfTwoFibresStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_family_localDomain_of_twoFibres : ∀ g n : ℕ, n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [Field o] [CharZero o] (ζ : oˣ) (W : Type) [CommRing W] [IsDomain W] [IsNoetherianRing W] [IsLocalRing W] (β : o →+* W) (v : (Fin (2 * g) → ZMod ((n ^ j) ^ 2)) → W) (K₀ K₁ : Type) [Field K₀] [IsAlgClosed K₀] [Field K₁] [IsAlgClosed K₁] (i₀ : W →+* K₀) (i₁ : W →+* K₁), (∀ q : Ideal W, q.IsPrime → q = RingHom.ker i₀ ∨ q = RingHom.ker i₁) → ∀ (P₀ : PolAV (Sp K₀)) (P₁ : PolAV (Sp K₁)) (h₀ : P₀.g = g) (h₁ : P₁.g = g) (l₀ : Out.Level P₀ ((n ^ j) ^ 2) (unitOn (Units.map (i₀.comp β).toMonoidHom ζ))) (l₁ : Out.Level P₁ ((n ^ j) ^ 2) (unitOn (Units.map (i₁.comp β).toMonoidHom ζ))), (IsThetaPt P₀ (n ^ j) (levelPoint l₀ h₀) fun a => fnOf (i₀ (v a))) → (IsThetaPt P₁ (n ^ j) (levelPoint l₁ h₁) fun a => fnOf (i₁ (v a))) → ∃ (P : PolAV (Sp W)) (pt : (Fin (2 * g) → ZMod ((n ^ j) ^ 2)) → (baseOver (Sp W) ⟶ P.A)) (φ₀ : P₀.A.left ⟶ P.A.left) (φ₁ : P₁.A.left ⟶ P.A.left), P.g = g ∧ (∀ a, pt a ^ ((n ^ j) ^ 2) = 1) ∧ IsGrpPullback P₀.A P.A (spMap i₀) φ₀ ∧ IsGrpPullback P₁.A P.A (spMap i₁) φ₁ ∧ LBIso P₀.L (P.L.pull φ₀) ∧ LBIso P₁.L (P.L.pull φ₁) ∧ (∀ a, (levelPoint l₀ h₀ a).left ≫ φ₀ = spMap i₀ ≫ (pt a).left) ∧ ∀ a, (levelPoint l₁ h₁ a).left ≫ φ₁ = spMap i₁ ≫ (pt a).left := by
  first | exact @GlobalTheory.MBLow.exists_family_of_two_fibres | exact GlobalTheory.MBLow.exists_family_of_two_fibres | (intros; apply GlobalTheory.MBLow.exists_family_of_two_fibres <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyRuleConstantAlongDeformationOfClauses
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MBLow.KeyTop

theorem levelPoint_cast {S : Scheme.{0}} {P : PolAV S} {M : ℕ} {u₁ u₂ : Γ(S, ⊤)ˣ} (h : u₁ = u₂)
    (l : Out.Level P M u₁) {g : ℕ} (hg : P.g = g) : levelPoint (h ▸ l) hg = levelPoint l hg := by
  subst h; rfl

theorem exhaust {K : Type} [Field K] [IsAlgClosed K] {P : PolAV (Sp K)} {M : ℕ} {ze : Γ(Sp K, ⊤)ˣ}
    (lev : Out.Level P M ze) {g : ℕ} (hg : P.g = g) (z : baseOver (Sp K) ⟶ P.A) (hz : z ^ M = 1) :
    ∃ a, levelPoint lev hg a = z := by
  subst hg
  obtain ⟨c, hc⟩ := lev.span K (𝟙 _) z hz
  refine ⟨fun i => ((c i : ℕ) : ZMod M), ?_⟩
  rw [levelPoint_rfl, Out.Level.toPt, ← hc]
  congr 1
  funext i; exact ZMod.val_cast_of_lt (c i).isLt

end GlobalTheory.MBLow.KeyTop

namespace GlobalTheory.MBLow.KeyTop

theorem transfer_of_rule4 : ∀ κ : Rule, Rule4 κ → Transfer κ := by
  intro κ hκ g n hn hodd
  obtain ⟨j₁, hj₁⟩ := GlobalTheory.T.exists_family_localDomain_of_twoFibres g n hn hodd
  refine ⟨max j₁ 1, fun j hj C _ _ _ _ _ e x hg ζ lev k hD => ?_⟩
  have hj1 : j₁ ≤ j := le_trans (le_max_left _ _) hj
  have hj2 : 1 ≤ j := le_trans (le_max_right _ _) hj
  have hmodd : Odd (n ^ j) := hodd.pow
  have hm3 : 3 ≤ n ^ j := by
    have h2 := hn.two_le
    have hne : n ≠ 2 := fun h => by subst h; exact (Nat.not_even_iff_odd.mpr hodd) even_two
    have := Nat.le_self_pow (show j ≠ 0 by omega) n
    omega
  obtain ⟨Θ, Γ, π, b, hπ, hb, hJ, ε, hε, hD'⟩ := hD
  haveI : NeZero ((n ^ j) ^ 2) := ⟨pow_ne_zero _ (pow_ne_zero _ hn.ne_zero)⟩
  let Φ : (Fin (2 * g) → ZMod ((n ^ j) ^ 2)) ⊕ (Fin (2 * g) → ZMod ((n ^ j) ^ 2)) × Fin g → PowerSeries C :=
    Sum.elim Θ (fun p => Γ p.1 p.2)
  let c : Fin 2 → C := ![(ζ : C), k]
  have hbΦ : ∀ a n, ‖PowerSeries.coeff n (Φ a)‖ ≤ b := by
    rintro (a | ⟨a, i⟩) n
    · exact (hb a n).1
    · exact (hb a n).2 i
  have hsΦ : ∀ u : ℂ, u ≠ 0 → ‖u‖ < ε → ∀ a, Summable fun n => ‖e (PowerSeries.coeff n (Φ a)) * u ^ n‖ := by
    intro u hu hu'
    obtain ⟨hs, -⟩ := hD' u hu hu'
    rintro (a | ⟨a, i⟩)
    · exact (hs a).1
    · exact (hs a).2 i
  obtain ⟨u, o, _, _, jo, c₀, hu0, huε, hc₀, W, _, _, _, _, _, _, β, i₀, i₁, φ, hinj, h0, h1, hunit, hprime, hφ⟩ :=
    GlobalTheory.T.exists_deformation_base_ring_local_domain C e _ (Fin 2) Φ c π b ε hπ hε hbΦ hsΦ
  obtain ⟨-, x₀, hg₀, lev₀, hJ₀, hκ₀⟩ := hD' u hu0 huε
  have hc0 : jo (c₀ 0) = ζ := hc₀ 0
  have hc1 : jo (c₀ 1) = k := hc₀ 1
  have hζ0 : c₀ 0 ≠ 0 := fun h => ζ.ne_zero (by rw [← hc0, h, map_zero])
  let ζ₀ : oˣ := Units.mk0 (c₀ 0) hζ0
  have hu₁ : Units.map (i₁.comp β).toMonoidHom ζ₀ = ζ := Units.ext (by
    show (i₁.comp β) (c₀ 0) = ζ
    rw [h1, hc0])
  have hu₀ : Units.map (i₀.comp β).toMonoidHom ζ₀ = Units.map e.toMonoidHom ζ := Units.ext (by
    show (i₀.comp β) (c₀ 0) = e ζ
    rw [h0, RingHom.comp_apply, hc0])
  have hl₀ := (congrArg unitOn hu₀).symm
  have hl₁ := (congrArg unitOn hu₁).symm
  let l₀ := hl₀ ▸ lev₀
  let l₁ := hl₁ ▸ lev
  have eϑ₀ : (fun a => ∑' n, e (PowerSeries.coeff n (Θ a)) * u ^ n) = fun a => i₀ (φ (Sum.inl a)) :=
    funext fun a => ((hφ (Sum.inl a)).1).symm
  have eJ₀ : (fun a i => ∑' n, e (PowerSeries.coeff n (Γ a i)) * u ^ n) = fun a i => i₀ (φ (Sum.inr (a, i))) :=
    funext fun a => funext fun i => ((hφ (Sum.inr (a, i))).1).symm
  have eϑ₁ : (fun a => ∑' n, PowerSeries.coeff n (Θ a) * π ^ n) = fun a => i₁ (φ (Sum.inl a)) :=
    funext fun a => ((hφ (Sum.inl a)).2).symm
  have eJ₁ : (fun a i => ∑' n, PowerSeries.coeff n (Γ a i) * π ^ n) = fun a i => i₁ (φ (Sum.inr (a, i))) :=
    funext fun a => funext fun i => ((hφ (Sum.inr (a, i))).2).symm
  rw [eϑ₀, eJ₀, ← levelPoint_cast hl₀ lev₀ hg₀] at hJ₀
  rw [eϑ₁, eJ₁, ← levelPoint_cast hl₁ lev hg] at hJ
  have hθ₀ := GlobalTheory.T.isThetaPt_of_thetaConstantsAndFirstJets ℂ x₀ g hg₀ (n ^ j) hmodd (by exact_mod_cast pow_ne_zero _ hn.ne_zero) _ _ _ _ hJ₀
  have hθ₁ := GlobalTheory.T.isThetaPt_of_thetaConstantsAndFirstJets C x g hg (n ^ j) hmodd (by exact_mod_cast pow_ne_zero _ hn.ne_zero) _ _ _ _ hJ
  obtain ⟨P, pt, φ₀, φ₁, hPg, hpt, hpb₀, hpb₁, hL₀, hL₁, hc₀', hc₁'⟩ :=
    hj₁ j hj1 o ζ₀ W β (fun a => φ (Sum.inl a)) ℂ C i₀ i₁ hprime x₀.P x.P hg₀ hg l₀ l₁ hθ₀ hθ₁
  have hk₀ : (κ ℂ x₀ : ℂ) = i₀ (β (c₀ 1)) := by
    rw [hκ₀, ← RingHom.comp_apply i₀ β, h0, RingHom.comp_apply, hc1]
  have := GlobalTheory.T.thetaKeyValue_two_fibres_local_ring κ hκ W ℂ C i₀ i₁ hinj hunit P x₀ x g hg₀ hg (n ^ j) hPg hmodd hm3 _ pt
    (levelPoint l₀ hg₀) (levelPoint l₁ hg) φ₀ φ₁ hpt hpb₀ hpb₁ hL₀ hL₁ hc₀' hc₁'
    (fun z hz => exhaust l₁ hg z hz) _ _ (β (c₀ 1)) hJ₀ hJ hk₀
  rw [this, ← RingHom.comp_apply i₁ β, h1, hc1]

end GlobalTheory.MBLow.KeyTop
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyRuleConstantAlongDeformationOfClausesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transfer_of_rule4' : ∀ κ : Rule, Rule4 κ → Transfer κ := by
  first | exact @GlobalTheory.MBLow.KeyTop.transfer_of_rule4 | exact GlobalTheory.MBLow.KeyTop.transfer_of_rule4 | (intros; apply GlobalTheory.MBLow.KeyTop.transfer_of_rule4 <;> assumption)
end
