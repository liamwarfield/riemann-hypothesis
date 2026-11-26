module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoMulInvOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.KerInfIntegrableOfMemRspan
noncomputable section

open NumberField IsDedekindDomain MeasureTheory

namespace GlobalTheory.JSW.RapidModel

open GlobalTheory.CuspRep GlobalTheory.JSW

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}


omit [_root_.NumberField.IsTotallyComplex E] in
theorem norm_toL_mul (x y : Matrix (Fin a) (Fin a) (Cinf E)) : ‖toL (x * y)‖ ≤ a * (‖toL x‖ * ‖toL y‖) := by
  refine pi_norm_le_iff_of_nonneg (by positivity) |>.2 fun i => pi_norm_le_iff_of_nonneg (by positivity) |>.2 fun j => ?_
  change ‖(x * y) i j‖ ≤ _
  rw [Matrix.mul_apply]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ (‖toL x‖ * ‖toL y‖) fun l _ => ?_).trans_eq (by simp))
  exact (norm_mul_le _ _).trans (mul_le_mul ((norm_le_pi_norm (toL x i) l).trans (norm_le_pi_norm (toL x) i))
    ((norm_le_pi_norm (toL y l) j).trans (norm_le_pi_norm (toL y) l)) (norm_nonneg _) (norm_nonneg _))


omit [_root_.NumberField.IsTotallyComplex E] in
theorem height_mul_le (x y : GL (Fin a) (Cinf E)) : height (x * y) ≤ (1 + 2 * a) * (height x * height y) := by
  have h1 := norm_toL_mul x.val y.val
  have h2 := norm_toL_mul (y⁻¹).val (x⁻¹).val
  have hx := one_le_height x
  have hy := one_le_height y
  have a1 : ‖toL x.val‖ ≤ height x := by unfold height; linarith [norm_nonneg (toL (x⁻¹).val)]
  have a2 : ‖toL (x⁻¹).val‖ ≤ height x := by unfold height; linarith [norm_nonneg (toL x.val)]
  have b1 : ‖toL y.val‖ ≤ height y := by unfold height; linarith [norm_nonneg (toL (y⁻¹).val)]
  have b2 : ‖toL (y⁻¹).val‖ ≤ height y := by unfold height; linarith [norm_nonneg (toL y.val)]
  have c1 : ‖toL x.val‖ * ‖toL y.val‖ ≤ height x * height y := mul_le_mul a1 b1 (norm_nonneg _) (by linarith)
  have c2 : ‖toL (y⁻¹).val‖ * ‖toL (x⁻¹).val‖ ≤ height x * height y := by
    rw [mul_comm]; exact mul_le_mul a2 b2 (norm_nonneg _) (by linarith)
  have c0 : 1 ≤ height x * height y := one_le_mul_of_one_le_of_one_le hx hy
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have e : height (x * y) = 1 + ‖toL (x.val * y.val)‖ + ‖toL ((y⁻¹).val * (x⁻¹).val)‖ := by
    unfold height; rw [mul_inv_rev]; rfl
  rw [e]
  nlinarith [mul_le_mul_of_nonneg_left c1 ha, mul_le_mul_of_nonneg_left c2 ha]


variable (E a) in
def modGr : Submodule ℂ (GA E a → ℂ) where
  carrier := {F | ∀ g, Measurable (chart F g) ∧ ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ y, ‖F (g * infGL E a y)‖ ≤ C * height y ^ N}
  add_mem' := fun {F G} hF hG g => by
    obtain ⟨m1, C, N, h0, h1⟩ := hF g
    obtain ⟨m2, C', N', h0', h2⟩ := hG g
    refine ⟨?_, C + C', N + N', by positivity, fun y => ?_⟩
    · have e : chart (F + G) g = fun x => chart F g x + chart G g x := by
        funext x
        by_cases h : IsUnit (Matrix.of x) <;> simp [chart, h]
      rw [e]; exact m1.add m2
    · have hy := one_le_height y
      have p1 : height y ^ N ≤ height y ^ (N + N') := pow_le_pow_right₀ hy (by omega)
      have p2 : height y ^ N' ≤ height y ^ (N + N') := pow_le_pow_right₀ hy (by omega)
      refine (norm_add_le _ _).trans ?_
      nlinarith [h1 y, h2 y, mul_le_mul_of_nonneg_left p1 h0, mul_le_mul_of_nonneg_left p2 h0']
  zero_mem' g := ⟨by
      have e : chart (0 : GA E a → ℂ) g = fun _ => 0 := by funext x; simp [chart]
      rw [e]; exact measurable_const, 0, 0, le_rfl, fun y => by simp⟩
  smul_mem' c F hF g := by
    obtain ⟨m1, C, N, h0, h1⟩ := hF g
    refine ⟨?_, ‖c‖ * C, N, by positivity, fun y => ?_⟩
    · have e : chart (c • F) g = fun x => c * chart F g x := by
        funext x
        by_cases h : IsUnit (Matrix.of x) <;> simp [chart, h]
      rw [e]; exact m1.const_mul c
    · rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_assoc]
      exact mul_le_mul_of_nonneg_left (h1 y) (norm_nonneg _)

theorem integrable_of_modGr {F : GA E a → ℂ} (hF : F ∈ modGr E a) {X : Type} [MeasurableSpace X] {ν : Measure X}
    {k : X → ℂ} {γ : X → GL (Fin a) (Cinf E)} (hk : IsRapidInf ν k γ) (g : GA E a) :
    Integrable (fun x => k x * F (g * infGL E a (γ x))) ν := by
  obtain ⟨m, C, N, h0, hC⟩ := hF g
  have h : Measurable fun x => toL (γ x).val := hk.2.1
  have e : (fun x => F (g * infGL E a (γ x))) = fun x => chart F g (toL (γ x).val) :=
    funext fun x => (chart_val F g (γ x)).symm
  have hm : Measurable fun x => F (g * infGL E a (γ x)) := by rw [e]; exact m.comp h
  refine ((hk.2.2 N).const_mul C).mono' (hk.1.mul hm).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
  rw [norm_mul]
  calc ‖k x‖ * ‖F (g * infGL E a (γ x))‖ ≤ ‖k x‖ * (C * height (γ x) ^ N) :=
        mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)
    _ = C * (‖k x‖ * height (γ x) ^ N) := by ring

theorem rspan_le_modGr (π : CuspSub E a) : rspan π ≤ modGr E a := by
  refine rspan_le (fun φ hφ g => ⟨measurable_chart φ.2 g, ?_⟩) (fun F hF h g => ?_) fun F hF X _ ν _ k γ hk g => ?_
  · obtain ⟨C, N, hC⟩ := (π.cusp φ hφ).1.growth g
    exact ⟨|C|, N, abs_nonneg C, fun y => (hC y).trans
      (mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg (by linarith [one_le_height y]) N))⟩
  · rw [← infGL_mul_finGL h]
    set y := Matrix.GeneralLinearGroup.map (pInf E) h
    set k := Matrix.GeneralLinearGroup.map (pFin E) h
    obtain ⟨m, C, N, h0, hC⟩ := hF (g * finGL E a k)
    refine ⟨?_, C * ((1 + 2 * a) * height y) ^ N, N, by have := one_le_height y; positivity, fun z => ?_⟩
    · have e : (fun x => F (x * (infGL E a y * finGL E a k))) =
          fun x => (fun x => F (x * finGL E a k)) (x * infGL E a y) := by
        funext x; simp only [mul_assoc]
      rw [e, chart_rt_inf (fun x => F (x * finGL E a k)), chart_rt_fin]
      exact m.comp (rmul (toL y.val)).continuous.measurable
    · have e : g * infGL E a z * (infGL E a y * finGL E a k) = g * finGL E a k * infGL E a (z * y) := by
        rw [mul_assoc g (finGL E a k), ← infGL_comm, map_mul]; simp only [mul_assoc]
      change ‖F (g * infGL E a z * (infGL E a y * finGL E a k))‖ ≤ _
      rw [e]
      refine (hC _).trans ?_
      rw [mul_assoc C, ← mul_pow]
      refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith [one_le_height (z * y)]) ?_ N) h0
      exact (height_mul_le z y).trans_eq (by ring)
  · obtain ⟨m, C, N, h0, hC⟩ := hF g
    refine ⟨?_, C * (1 + 2 * a) ^ N * ∫ x, ‖k x‖ * height (γ x) ^ N ∂ν, N, ?_, fun z => ?_⟩
    · have e : chart (kerInf ν k γ F) g = fun x => ∫ t, k t * chart F g (toL (Matrix.of x * (γ t).val)) ∂ν := by
        funext x
        by_cases h : IsUnit (Matrix.of x)
        · obtain ⟨u, hu⟩ := h
          have hx : x = (toL u.val) := hu.symm
          rw [hx, chart_val, kerInf]
          congr 1
          funext t
          rw [mul_assoc, ← map_mul, ← chart_val F g]
          rfl
        · have h' : ∀ t, ¬ IsUnit (Matrix.of (toL (Matrix.of x * (γ t).val))) :=
            fun t h' => h ((Units.isUnit_mul_units _ (γ t)).1 h')
          simp only [chart, dif_neg h, dif_neg (h' _), mul_zero, integral_zero]
      rw [e]
      have hγ : Measurable fun x => toL (γ x).val := hk.2.1
      have hm : Measurable fun p : Lie E a × X => toL (Matrix.of p.1 * (γ p.2).val) := by
        refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
        change Measurable fun p : Lie E a × X => (Matrix.of p.1 * (γ p.2).val) i j
        simp only [Matrix.mul_apply]
        refine Finset.measurable_sum _ fun l _ => Measurable.mul ?_ ?_
        · exact (measurable_pi_apply l).comp ((measurable_pi_apply i).comp measurable_fst)
        · exact (measurable_pi_apply j).comp ((measurable_pi_apply l).comp (hγ.comp measurable_snd))
      have hs : StronglyMeasurable fun p : Lie E a × X => k p.2 * chart F g (toL (Matrix.of p.1 * (γ p.2).val)) :=
        ((hk.1.comp measurable_snd).mul (m.comp hm)).stronglyMeasurable
      exact hs.integral_prod_right'.measurable
    · refine mul_nonneg (by positivity) (integral_nonneg fun x => ?_)
      have := one_le_height (γ x)
      positivity
    · rw [kerInf]
      have hz := one_le_height z
      calc _ ≤ ∫ x, (C * (1 + 2 * a) ^ N * height z ^ N) * (‖k x‖ * height (γ x) ^ N) ∂ν := by
            refine norm_integral_le_of_norm_le ((hk.2.2 N).const_mul _) (Filter.Eventually.of_forall fun x => ?_)
            rw [norm_mul, mul_assoc g, ← map_mul]
            have h1 := (hC (z * γ x)).trans (mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ (by linarith [one_le_height (z * γ x)]) (height_mul_le z (γ x)) N) h0)
            refine (mul_le_mul_of_nonneg_left h1 (norm_nonneg _)).trans_eq ?_
            rw [mul_pow, mul_pow]; ring
        _ = _ := by rw [integral_const_mul]; ring

end GlobalTheory.JSW.RapidModel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactUniformBound
namespace GlobalTheory.CompactUniformHeightBound

open Filter Topology

theorem height_one_le {E : Type} [Field E] [NumberField E] {a : ℕ}
    (y : GL (Fin a) (GlobalTheory.CuspRep.Cinf E)) : 1 ≤ GlobalTheory.CuspRep.height y := by
  unfold GlobalTheory.CuspRep.height
  exact le_add_of_le_of_nonneg (le_add_of_nonneg_right (norm_nonneg _)) (norm_nonneg _)

theorem compact_uniform_bound : (let d1 : {E : Type} → [inst : Field E] → [inst_1 : NumberField E] → [NumberField.IsTotallyComplex E] → {a : ℕ} → (GlobalTheory.CuspRep.GA E a → ℂ) → Prop := @(fun {E : Type} [Field E] [NumberField E] [NumberField.IsTotallyComplex E] {a : ℕ} (F : GlobalTheory.CuspRep.GA E a → ℂ) ↦ ∀ (g₀ : GlobalTheory.CuspRep.GA E a), ∃ (C : ℝ) (N : ℕ), (0 : ℝ) ≤ C ∧ ∀ᶠ (g : GlobalTheory.CuspRep.GA E a) in nhds g₀, ∀ (y : GL (Fin a) (GlobalTheory.CuspRep.Cinf E)), ‖F (g * (GlobalTheory.CuspRep.infGL E a : GL (Fin a) (GlobalTheory.CuspRep.Cinf E) → GlobalTheory.CuspRep.GA E a) y)‖ ≤ C * GlobalTheory.CuspRep.height y ^ N); ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : NumberField.IsTotallyComplex E] {a : ℕ} {F : GlobalTheory.CuspRep.GA E a → ℂ}, d1 F → ∀ {K : Set (GlobalTheory.CuspRep.GA E a)}, IsCompact K → ∃ (C : ℝ) (N : ℕ), (0 : ℝ) ≤ C ∧ ∀ g ∈ K, ∀ (y : GL (Fin a) (GlobalTheory.CuspRep.Cinf E)), ‖F (g * (GlobalTheory.CuspRep.infGL E a : GL (Fin a) (GlobalTheory.CuspRep.Cinf E) → GlobalTheory.CuspRep.GA E a) y)‖ ≤ C * GlobalTheory.CuspRep.height y ^ N) := by
  intro d1 E _ _ _ a F hF K hK
  have hb : ∀ g₀ : GlobalTheory.CuspRep.GA E a, ∃ (C : ℝ) (N : ℕ), (0 : ℝ) ≤ C ∧
      {g : GlobalTheory.CuspRep.GA E a | ∀ (y : GL (Fin a) (GlobalTheory.CuspRep.Cinf E)),
        ‖F (g * (GlobalTheory.CuspRep.infGL E a : GL (Fin a) (GlobalTheory.CuspRep.Cinf E) → GlobalTheory.CuspRep.GA E a) y)‖
          ≤ C * GlobalTheory.CuspRep.height y ^ N} ∈ 𝓝 g₀ := fun g₀ => hF g₀
  choose C N hC hU using hb
  obtain ⟨t, -, hKt⟩ := hK.elim_nhds_subcover _ (fun x _ => hU x)
  refine ⟨∑ x ∈ t, C x, t.sup N, Finset.sum_nonneg (fun x _ => hC x), ?_⟩
  intro g hg y
  obtain ⟨x, hx, hgx⟩ := Set.mem_iUnion₂.mp (hKt hg)
  have h1 := height_one_le y
  calc _ ≤ C x * GlobalTheory.CuspRep.height y ^ N x := hgx y
    _ ≤ (∑ i ∈ t, C i) * GlobalTheory.CuspRep.height y ^ t.sup N :=
      mul_le_mul (Finset.single_le_sum (fun i _ => hC i) hx)
        (pow_le_pow_right₀ h1 (Finset.le_sup hx))
        (pow_nonneg (zero_le_one.trans h1) _) (Finset.sum_nonneg fun i _ => hC i)

end GlobalTheory.CompactUniformHeightBound
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormModerateGrowthCompact
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Topology Filter Matrix

namespace GlobalTheory.JSW.MirSemi

open GlobalTheory.CuspRep GlobalTheory.JSW

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

def IsLocModerate (F : GA E a → ℂ) : Prop :=
  ∀ g₀ : GA E a, ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ᶠ g in 𝓝 g₀, ∀ y, ‖F (g * infGL E a y)‖ ≤ C * height y ^ N

theorem continuous_mapGL {R S : Type} [CommRing R] [CommRing S] [TopologicalSpace R] [TopologicalSpace S]
    [IsTopologicalRing R] [IsTopologicalRing S] {p : R →+* S} (hp : Continuous p) :
    Continuous (GeneralLinearGroup.map (n := Fin a) p) :=
  Continuous.units_map _ (continuous_id.matrix_map hp)

theorem continuous_pInf_ad : Continuous (pInf E) := by
  have h : Continuous (infEq E).symm := by
    refine continuous_pi fun w => ?_
    exact (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      (continuous_apply w)
  exact h.comp continuous_fst

theorem continuous_pFin_ad : Continuous (pFin E) := continuous_snd

theorem continuous_height_inf : Continuous (height : GL (Fin a) (Cinf E) → ℝ) := by
  have ht : Continuous fun x : Matrix (Fin a) (Fin a) (Cinf E) => toL x := continuous_id
  show Continuous fun y : GL (Fin a) (Cinf E) => 1 + ‖toL y.val‖ + ‖toL (y⁻¹).val‖
  exact (continuous_const.add (ht.comp Units.continuous_val).norm).add (ht.comp Units.continuous_coe_inv).norm

theorem isAutForm_continuous_locModerate {φ : Sm E a} (hA : IsAutForm φ) : Continuous φ.1 ∧ IsLocModerate φ.1 := by
  have cI : Continuous fun g : GA E a => GeneralLinearGroup.map (pInf E) g := continuous_mapGL continuous_pInf_ad
  have cF : Continuous fun g : GA E a => GeneralLinearGroup.map (pFin E) g := continuous_mapGL continuous_pFin_ad
  have dec : ∀ g₀ g : GA E a, finRep E a (GeneralLinearGroup.map (pFin E) (g₀⁻¹ * g)) φ = φ → ∀ y,
      φ.1 (g * infGL E a y) = φ.1 (g₀ * infGL E a (GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g) * y)) := by
    intro g₀ g hk y
    have hu : g = g₀ * (infGL E a (GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g)) *
        finGL E a (GeneralLinearGroup.map (pFin E) (g₀⁻¹ * g))) := by
      rw [infGL_mul_finGL, mul_inv_cancel_left]
    have e : g * infGL E a y = g₀ * infGL E a (GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g) * y) *
        finGL E a (GeneralLinearGroup.map (pFin E) (g₀⁻¹ * g)) := by
      conv_lhs => rw [hu]
      rw [map_mul (infGL E a) (GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g)) y]
      simp only [mul_assoc]
      rw [← infGL_comm]
    rw [e]
    exact congrArg (fun ψ : Sm E a => ψ.1 (g₀ * infGL E a (GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g) * y))) hk
  have nb : ∀ g₀ : GA E a, ∀ᶠ g in 𝓝 g₀, finRep E a (GeneralLinearGroup.map (pFin E) (g₀⁻¹ * g)) φ = φ := by
    intro g₀
    have hc : Continuous fun g : GA E a => GeneralLinearGroup.map (pFin E) (g₀⁻¹ * g) :=
      cF.comp (continuous_const.mul continuous_id)
    refine hc.continuousAt.preimage_mem_nhds (hA.level.mem_nhds ?_)
    simp
  refine ⟨continuous_iff_continuousAt.2 fun g₀ => ?_, fun g₀ => ?_⟩
  · have e : (fun g => φ.1 g) =ᶠ[𝓝 g₀]
        fun g => chart φ.1 g₀ (toL (GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g)).val) := by
      filter_upwards [nb g₀] with g hg
      rw [chart_val]
      have := dec g₀ g hg 1
      simp only [map_one, mul_one] at this
      exact this
    refine ContinuousAt.congr ?_ e.symm
    refine ContinuousAt.comp_of_eq (contDiffAt_chart (x := oneL E a) φ.2 g₀ isUnit_one).continuousAt ?_
      (by simp [oneL])
    have ht : Continuous fun x : Matrix (Fin a) (Fin a) (Cinf E) => toL x := continuous_id
    exact ((ht.comp Units.continuous_val).comp (cI.comp (continuous_const.mul continuous_id))).continuousAt
  · obtain ⟨C, N, hC⟩ := hA.growth g₀
    have ha : (0 : ℝ) ≤ 1 + 2 * a := by positivity
    have h1' := one_le_height (1 : GL (Fin a) (Cinf E))
    refine ⟨|C| * ((1 + 2 * a) * (height (1 : GL (Fin a) (Cinf E)) + 1)) ^ N, N,
      mul_nonneg (abs_nonneg C) (pow_nonneg (mul_nonneg ha (by linarith)) N), ?_⟩
    have hh : ∀ᶠ g in 𝓝 g₀, height (GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g)) <
        height (1 : GL (Fin a) (Cinf E)) + 1 := by
      have hc : Continuous fun g : GA E a => height (GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g)) :=
        continuous_height_inf.comp (cI.comp (continuous_const.mul continuous_id))
      exact hc.continuousAt.eventually_lt continuousAt_const (by simp)
    filter_upwards [nb g₀, hh] with g hg hg' y
    rw [dec g₀ g hg y]
    have h1 := one_le_height (GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g))
    have h2 := one_le_height y
    have h3 := one_le_height (GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g) * y)
    calc ‖φ.1 (g₀ * infGL E a (GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g) * y))‖
        ≤ C * height (GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g) * y) ^ N := hC _
      _ ≤ |C| * height (GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g) * y) ^ N :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg (by linarith) N)
      _ ≤ |C| * ((1 + 2 * a) * (height (GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g)) * height y)) ^ N :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) (RapidModel.height_mul_le _ y) N) (abs_nonneg C)
      _ ≤ |C| * (((1 + 2 * a) * (height (1 : GL (Fin a) (Cinf E)) + 1)) * height y) ^ N := by
          refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀
            (mul_nonneg ha (mul_nonneg (by linarith) (by linarith))) ?_ N) (abs_nonneg C)
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hg'.le ha) (by linarith)
      _ = _ := by rw [mul_pow]; ring


variable (π : CuspSub E a) in
def regSpan : Submodule ℂ (GA E a → ℂ) where
  carrier := {F | F ∈ rspan π ∧ Continuous F ∧ IsLocModerate F}
  add_mem' := fun {F G} hF hG => by
    refine ⟨add_mem hF.1 hG.1, hF.2.1.add hG.2.1, fun g₀ => ?_⟩
    obtain ⟨C, N, h0, e1⟩ := hF.2.2 g₀
    obtain ⟨C', N', h0', e2⟩ := hG.2.2 g₀
    refine ⟨C + C', N + N', add_nonneg h0 h0', ?_⟩
    filter_upwards [e1, e2] with g h1 h2 y
    have hy := one_le_height y
    have p1 : height y ^ N ≤ height y ^ (N + N') := pow_le_pow_right₀ hy (by omega)
    have p2 : height y ^ N' ≤ height y ^ (N + N') := pow_le_pow_right₀ hy (by omega)
    refine (norm_add_le _ _).trans ?_
    nlinarith [h1 y, h2 y, mul_le_mul_of_nonneg_left p1 h0, mul_le_mul_of_nonneg_left p2 h0']
  zero_mem' := ⟨zero_mem _, continuous_zero, fun _ => ⟨0, 0, le_rfl, Eventually.of_forall fun _ _ => by simp⟩⟩
  smul_mem' c F hF := by
    refine ⟨Submodule.smul_mem _ c hF.1, hF.2.1.const_smul c, fun g₀ => ?_⟩
    obtain ⟨C, N, h0, e⟩ := hF.2.2 g₀
    refine ⟨‖c‖ * C, N, mul_nonneg (norm_nonneg _) h0, ?_⟩
    filter_upwards [e] with g h y
    rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (h y) (norm_nonneg _)

theorem mem_regSpan {π : CuspSub E a} {F : GA E a → ℂ} :
    F ∈ regSpan π ↔ F ∈ rspan π ∧ Continuous F ∧ IsLocModerate F := Iff.rfl

theorem rt_mem_regSpan {π : CuspSub E a} {F : GA E a → ℂ} (hF : F ∈ regSpan π) (h : GA E a) :
    (fun g => F (g * h)) ∈ regSpan π := by
  refine ⟨rt_mem_rspan hF.1 h, hF.2.1.comp (continuous_mul_const h), fun g₀ => ?_⟩
  obtain ⟨y₀, k, rfl⟩ : ∃ y₀ k, h = infGL E a y₀ * finGL E a k := ⟨_, _, (infGL_mul_finGL h).symm⟩
  obtain ⟨C, N, h0, e⟩ := hF.2.2 (g₀ * finGL E a k)
  have hy₀ := one_le_height y₀
  refine ⟨C * ((1 + 2 * a) * height y₀) ^ N, N, mul_nonneg h0 (pow_nonneg (mul_nonneg (by positivity)
    (by linarith)) N), ?_⟩
  have ht : Tendsto (fun g => g * finGL E a k) (𝓝 g₀) (𝓝 (g₀ * finGL E a k)) := (continuous_mul_const _).tendsto g₀
  filter_upwards [ht.eventually e] with g hg z
  have ex : g * infGL E a z * (infGL E a y₀ * finGL E a k) = g * finGL E a k * infGL E a (z * y₀) := by
    rw [mul_assoc g (finGL E a k), ← infGL_comm, map_mul]; simp only [mul_assoc]
  change ‖F (g * infGL E a z * (infGL E a y₀ * finGL E a k))‖ ≤ _
  rw [ex]
  refine (hg _).trans ?_
  rw [mul_assoc C, ← mul_pow]
  refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith [one_le_height (z * y₀)]) ?_ N) h0
  exact (RapidModel.height_mul_le z y₀).trans_eq (by ring)

theorem kerInf_mem_regSpan {π : CuspSub E a} {F : GA E a → ℂ} (hF : F ∈ regSpan π) {X : Type} [MeasurableSpace X]
    (ν : Measure X) [SFinite ν] {k : X → ℂ} {γ : X → GL (Fin a) (Cinf E)} (hk : IsRapidInf ν k γ) :
    kerInf ν k γ F ∈ regSpan π := by
  have hM := RapidModel.rspan_le_modGr π hF.1
  refine ⟨kerInf_mem_rspan hF.1 ν hk, continuous_iff_continuousAt.2 fun g₀ => ?_, fun g₀ => ?_⟩
  · obtain ⟨C, N, h0, e⟩ := hF.2.2 g₀
    show ContinuousAt (fun g => ∫ x, k x * F (g * infGL E a (γ x)) ∂ν) g₀
    set_option synthInstance.maxHeartbeats 200000 in
    refine continuousAt_of_dominated (bound := fun x => C * (‖k x‖ * height (γ x) ^ N))
      (Eventually.of_forall fun g => (RapidModel.integrable_of_modGr hM hk g).aestronglyMeasurable) ?_
      ((hk.2.2 N).const_mul C)
      (Eventually.of_forall fun x => (continuous_const.mul (hF.2.1.comp (continuous_mul_const _))).continuousAt)
    filter_upwards [e] with g hg
    refine Eventually.of_forall fun x => ?_
    rw [norm_mul]
    calc ‖k x‖ * ‖F (g * infGL E a (γ x))‖ ≤ ‖k x‖ * (C * height (γ x) ^ N) :=
          mul_le_mul_of_nonneg_left (hg _) (norm_nonneg _)
      _ = C * (‖k x‖ * height (γ x) ^ N) := by ring
  · obtain ⟨C, N, h0, e⟩ := hF.2.2 g₀
    refine ⟨C * (1 + 2 * a) ^ N * ∫ x, ‖k x‖ * height (γ x) ^ N ∂ν, N, ?_, ?_⟩
    · refine mul_nonneg (by positivity) (integral_nonneg fun x => ?_)
      have := one_le_height (γ x)
      positivity
    · filter_upwards [e] with g hC z
      rw [kerInf]
      calc _ ≤ ∫ x, (C * (1 + 2 * a) ^ N * height z ^ N) * (‖k x‖ * height (γ x) ^ N) ∂ν := by
            refine norm_integral_le_of_norm_le ((hk.2.2 N).const_mul _) (Eventually.of_forall fun x => ?_)
            rw [norm_mul, mul_assoc g, ← map_mul]
            have h1 := (hC (z * γ x)).trans (mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ (by linarith [one_le_height (z * γ x)]) (RapidModel.height_mul_le z (γ x)) N) h0)
            refine (mul_le_mul_of_nonneg_left h1 (norm_nonneg _)).trans_eq ?_
            rw [mul_pow, mul_pow]; ring
        _ = _ := by rw [integral_const_mul]; ring

theorem IsLocModerate.bound_of_isCompact {F : GA E a → ℂ} (hF : IsLocModerate F) {K : Set (GA E a)}
    (hK : IsCompact K) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ g ∈ K, ∀ y, ‖F (g * infGL E a y)‖ ≤ C * height y ^ N := by
  first
  | exact @_root_.GlobalTheory.CompactUniformHeightBound.compact_uniform_bound
  | exact _root_.GlobalTheory.CompactUniformHeightBound.compact_uniform_bound
  | (apply _root_.GlobalTheory.CompactUniformHeightBound.compact_uniform_bound <;> assumption)
  | (intros; apply _root_.GlobalTheory.CompactUniformHeightBound.compact_uniform_bound <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CompactUniformHeightBound.compact_uniform_bound <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CompactUniformHeightBound.compact_uniform_bound ..)

theorem locSpan_le_regSpan {π : CuspSub E a} {φ : Sm E a} (hφ : φ ∈ π.V) (S : Finset (HeightOneSpectrum (𝓞 E))) :
    locSpan S φ.1 ≤ regSpan π :=
  locSpan_le (mem_regSpan.2 ⟨mem_rspan hφ, isAutForm_continuous_locModerate (π.cusp φ hφ).1⟩)
    (fun _ hF h _ => rt_mem_regSpan hF h) fun _ hF _ _ ν _ _ _ hk => kerInf_mem_regSpan hF ν hk

end GlobalTheory.JSW.MirSemi


open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory in
theorem GlobalTheory.JSW.MirSemi.locSpan_continuous_moderate :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E)))
      (π : CuspSub E a) (φ : Sm E a), φ ∈ π.V → ∀ F ∈ GlobalTheory.JSW.MirSemi.locSpan S φ.1, Continuous F ∧
        ∀ K : Set (GA E a), IsCompact K → ∃ (C : ℝ) (N : ℕ), ∀ g ∈ K, ∀ y : GL (Fin a) (Cinf E),
          ‖F (g * infGL E a y)‖ ≤ C * height y ^ N := by
  intro E _ _ _ a S π φ hφ F hF
  have hG := GlobalTheory.JSW.MirSemi.locSpan_le_regSpan hφ S hF
  refine ⟨hG.2.1, fun K hK => ?_⟩
  obtain ⟨C, N, -, h⟩ := hG.2.2.bound_of_isCompact hK
  exact ⟨C, N, h⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormModerateGrowthCompactStatement
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cusp_form_moderate_growth_compact : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (π : CuspSub E a) (φ : Sm E a), φ ∈ π.V → ∀ F ∈ GlobalTheory.JSW.MirSemi.locSpan S φ.1, Continuous F ∧ ∀ K : Set (GA E a), IsCompact K → ∃ (C : ℝ) (N : ℕ), ∀ g ∈ K, ∀ y : GL (Fin a) (Cinf E), ‖F (g * infGL E a y)‖ ≤ C * height y ^ N := by
  first | exact @GlobalTheory.JSW.MirSemi.locSpan_continuous_moderate | exact GlobalTheory.JSW.MirSemi.locSpan_continuous_moderate | (intros; apply GlobalTheory.JSW.MirSemi.locSpan_continuous_moderate <;> assumption)
end
