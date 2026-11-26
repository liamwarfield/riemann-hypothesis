module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfMemSmoothSpan
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameGenAtTransport

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MellinIntegralRapidDecayEntireOfLeOne
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MellinIntegralRapidDecayEntireOfLeOne
open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.ThetaPoisson GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped ComplexConjugate nonZeroDivisors ContDiff

namespace GlobalTheory

theorem integral_mul_cpow_of_rapid_decay_entire :
    ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) (δ : X → ℝ) (F : X → ℂ), Measurable δ →
      (∀ᵐ x ∂ν, 0 < δ x ∧ δ x ≤ 1) → Integrable δ ν → AEStronglyMeasurable F ν →
      (∀ K : ℕ, ∃ C : ℝ, ∀ᵐ x ∂ν, ‖F x‖ ≤ C * δ x ^ K) →
      (∀ s : ℂ, Integrable (fun x => F x * (δ x : ℂ) ^ s) ν) ∧
        Differentiable ℂ fun s : ℂ => ∫ x, F x * (δ x : ℂ) ^ s ∂ν := by
  intro X _ ν δ F hδm hδ hδi hF hdec
  have key : ∀ t : ℝ, ∃ C : ℝ, ∀ᵐ x ∂ν, ‖F x‖ * δ x ^ t ≤ C * δ x := by
    intro t
    obtain ⟨K, hK⟩ : ∃ K : ℕ, 1 - t ≤ K := exists_nat_ge (1 - t)
    obtain ⟨C, hC⟩ := hdec K
    refine ⟨C, ?_⟩
    filter_upwards [hC, hδ] with x hx hx'
    obtain ⟨h0, h1⟩ := hx'
    have hpK : 0 < δ x ^ K := pow_pos h0 K
    have hC0 : 0 ≤ C := by
      by_contra hc
      push_neg at hc
      have := mul_neg_of_neg_of_pos hc hpK
      linarith [norm_nonneg (F x)]
    have hpt : 0 ≤ δ x ^ t := Real.rpow_nonneg h0.le t
    calc ‖F x‖ * δ x ^ t ≤ C * δ x ^ K * δ x ^ t := mul_le_mul_of_nonneg_right hx hpt
      _ = C * δ x ^ ((K : ℝ) + t) := by rw [Real.rpow_add h0, Real.rpow_natCast]; ring
      _ ≤ C * δ x ^ (1 : ℝ) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge h0 h1 (by linarith)) hC0
      _ = C * δ x := by rw [Real.rpow_one]
  have hcm : ∀ s : ℂ, Measurable fun x => (δ x : ℂ) ^ s :=
    fun s => (Complex.measurable_ofReal.comp hδm).pow_const s
  have hmeas : ∀ s : ℂ, AEStronglyMeasurable (fun x => F x * (δ x : ℂ) ^ s) ν :=
    fun s => hF.mul (hcm s).aestronglyMeasurable
  have hint : ∀ s : ℂ, Integrable (fun x => F x * (δ x : ℂ) ^ s) ν := by
    intro s
    obtain ⟨C, hC⟩ := key s.re
    refine Integrable.mono' (hδi.const_mul C) (hmeas s) ?_
    filter_upwards [hC, hδ] with x hx hx'
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx'.1]
    exact hx
  refine ⟨hint, fun s₀ => ?_⟩
  obtain ⟨C, hC⟩ := key (s₀.re - 2)
  have hF'm : AEStronglyMeasurable
      (fun x => F x * ((δ x : ℂ) ^ s₀ * Complex.log (δ x))) ν :=
    hF.mul ((hcm s₀).mul (Complex.measurable_log.comp
      (Complex.measurable_ofReal.comp hδm))).aestronglyMeasurable
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν) (x₀ := s₀)
    (F := fun s x => F x * (δ x : ℂ) ^ s)
    (F' := fun s x => F x * ((δ x : ℂ) ^ s * Complex.log (δ x)))
    (bound := fun x => C * δ x) (Metric.ball_mem_nhds s₀ zero_lt_one)
    (Filter.Eventually.of_forall hmeas) (hint s₀) hF'm ?_ (hδi.const_mul C) ?_
  · exact hd.2.differentiableAt
  · filter_upwards [hC, hδ] with x hx hx'
    obtain ⟨h0, h1⟩ := hx'
    intro s hs
    rw [Metric.mem_ball, Complex.dist_eq] at hs
    have hre : s₀.re - 1 ≤ s.re := by
      have h := Complex.abs_re_le_norm (s - s₀)
      rw [Complex.sub_re] at h
      linarith [neg_abs_le (s.re - s₀.re)]
    have hlog : ‖Complex.log (δ x)‖ = |Real.log (δ x)| := by
      rw [← Complex.ofReal_log h0.le, Complex.norm_real, Real.norm_eq_abs]
    have hl := Real.abs_log_mul_self_lt (δ x) h0 h1
    rw [abs_mul, abs_of_pos h0] at hl
    have e1 : δ x ^ s.re ≤ δ x ^ (s₀.re - 1) := Real.rpow_le_rpow_of_exponent_ge h0 h1 hre
    have e2 : δ x ^ (s₀.re - 1) = δ x ^ (s₀.re - 2) * δ x := by
      rw [← Real.rpow_add_one h0.ne']; ring_nf
    have hp2 : 0 ≤ δ x ^ (s₀.re - 2) := Real.rpow_nonneg h0.le _
    have e3 : δ x ^ s.re * |Real.log (δ x)| ≤ δ x ^ (s₀.re - 2) := by
      calc δ x ^ s.re * |Real.log (δ x)| ≤ δ x ^ (s₀.re - 1) * |Real.log (δ x)| :=
            mul_le_mul_of_nonneg_right e1 (abs_nonneg _)
        _ = δ x ^ (s₀.re - 2) * (|Real.log (δ x)| * δ x) := by rw [e2]; ring
        _ ≤ δ x ^ (s₀.re - 2) * 1 := mul_le_mul_of_nonneg_left hl.le hp2
        _ = δ x ^ (s₀.re - 2) := mul_one _
    rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos h0, hlog]
    calc ‖F x‖ * (δ x ^ s.re * |Real.log (δ x)|) ≤ ‖F x‖ * δ x ^ (s₀.re - 2) :=
          mul_le_mul_of_nonneg_left e3 (norm_nonneg _)
      _ ≤ C * δ x := hx
  · filter_upwards [hδ] with x hx' s _
    exact ((Complex.hasStrictDerivAt_const_cpow (x := (δ x : ℂ)) (y := s)
      (Or.inl (Complex.ofReal_ne_zero.mpr hx'.1.ne'))).hasDerivAt).const_mul (F x)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MellinIntegralRapidDecayEntireOfLeOneStatement
open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.ThetaPoisson GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped ComplexConjugate nonZeroDivisors ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mellin_integral_rapidDecay_entire_of_le_one : ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) (δ : X → ℝ) (F : X → ℂ), Measurable δ → (∀ᵐ x ∂ν, 0 < δ x ∧ δ x ≤ 1) → Integrable δ ν → AEStronglyMeasurable F ν → (∀ K : ℕ, ∃ C : ℝ, ∀ᵐ x ∂ν, ‖F x‖ ≤ C * δ x ^ K) → (∀ s : ℂ, Integrable (fun x => F x * (δ x : ℂ) ^ s) ν) ∧ Differentiable ℂ fun s : ℂ => ∫ x, F x * (δ x : ℂ) ^ s ∂ν := by
  first | exact @GlobalTheory.integral_mul_cpow_of_rapid_decay_entire | exact GlobalTheory.integral_mul_cpow_of_rapid_decay_entire | (intros; apply GlobalTheory.integral_mul_cpow_of_rapid_decay_entire <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LastRowCongruenceDetWeightMeasurableInvariant
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LastRowCongruenceDetWeightMeasurableInvariant
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.RSJ GlobalTheory.MirTower GlobalTheory.CuspGeneric Formalism.L2.Host
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace GlobalTheory.ZUnfWt

open GlobalTheory.ZUnf

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {m : ℕ}


omit [_root_.NumberField.IsTotallyComplex E] in
theorem lastRow_mul_of_mem {h : GA E (m + 1)} (hh : h ∈ mirU (Ad E) (m + 1) m) (g : GA E (m + 1)) :
    GlobalTheory.ZEul.lastRow (h * g) = GlobalTheory.ZEul.lastRow g := by
  funext j
  simp only [GlobalTheory.ZEul.lastRow, Units.val_mul, Matrix.mul_apply]
  rw [Finset.sum_eq_single (Fin.last m)]
  · rw [(mem_mirU_last.1 hh) (Fin.last m), if_pos rfl, one_mul]
  · intro l _ hl
    rw [(mem_mirU_last.1 hh) l, if_neg hl, zero_mul]
  · simp


omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
theorem det_blkU {R : Type} [CommRing R] {a k : ℕ} (y : UnipotentBlockColumnIndex a k k → R) : (blkU y : GL (Fin a) R).val.det = 1 := by
  have h := mem_mirU_zero.1 (blkU_mem_mirU 0 y)
  rw [Matrix.det_of_upperTriangular (fun i j hij => h.1 i j hij)]
  simp [h.2]

omit [_root_.NumberField.IsTotallyComplex E] in
theorem detPow_blkU (x : ℝ) {k : ℕ} (y : UnipotentBlockColumnIndex (m + 1) k k → Ad E) : detPow E (m + 1) x (blkU y) = 1 := by
  have hd : Matrix.GeneralLinearGroup.det (blkU y : GA E (m + 1)) = 1 := Units.ext (det_blkU y)
  unfold detPow chiDet
  rw [MonoidHom.comp_apply, hd, map_one]
  simp


omit [_root_.NumberField.IsTotallyComplex E] in
theorem isClosed_natLat (N : ℕ) : IsClosed (natLat E N) := by
  haveI : T2Space (Af E) := inferInstanceAs (T2Space (RestrictedProduct _ _ _))
  have e : natLat E N = (fun z => (N : Af E) * z) '' (GroundTheory.Global.integralFiniteAdeles (𝓞 E) E : Set (Af E)) := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z, hz, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z, hz, rfl⟩
  rw [e]
  exact ((GroundTheory.Global.isCompact_integralFiniteAdeles E).image (continuous_const.mul continuous_id)).isClosed

omit [_root_.NumberField.IsTotallyComplex E] in
theorem continuous_yFin : Continuous (yFin (E := E) (m := m)) :=
  continuous_pi fun i => (continuous_snd : Continuous (GlobalTheory.RSJ.pFin E)).comp
    ((Units.continuous_val : Continuous fun g : GA E (m + 1) => (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E))).matrix_elem
      (Fin.last m) i)

omit [_root_.NumberField.IsTotallyComplex E] in
theorem continuous_detPow (x : ℝ) : Continuous (detPow E (m + 1) x) :=
  continuous_norm.comp (Units.continuous_val.comp
    ((GlobalTheory.HeckeGal.Model.absPow E x).2.1.comp Matrix.GeneralLinearGroup.continuous_det))

omit [_root_.NumberField.IsTotallyComplex E] in
theorem measurable_wt (N : ℕ) (x : ℝ) : Measurable (wt (E := E) (m := m) N x) := by
  let S : Set (Fin (m + 1) → Af E) := {y | ∀ i : Fin (m + 1), y i - (if (i : ℕ) + 1 = m + 1 then 1 else 0) ∈ natLat E N}
  have hS : IsClosed S := by
    have e : S = ⋂ i : Fin (m + 1),
        (fun y : Fin (m + 1) → Af E => y i - (if (i : ℕ) + 1 = m + 1 then 1 else 0)) ⁻¹' natLat E N := by
      ext y; simp [S]
    rw [e]
    exact isClosed_iInter fun i => (isClosed_natLat N).preimage ((continuous_apply i).sub continuous_const)
  have hm : MeasurableSet {g : GA E (m + 1) | yFin g ∈ S} := (hS.preimage continuous_yFin).measurableSet
  have hind : Measurable fun g : GA E (m + 1) => indN N (yFin g) := by
    unfold indN
    exact Measurable.ite hm measurable_const measurable_const
  exact ((Complex.measurable_re.comp hind).mul (continuous_detPow x).measurable).real_toNNReal

theorem wt_measurable_invariant : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m N : ℕ) (x : ℝ),
    Measurable (GlobalTheory.ZUnf.wt (E := E) (m := m) N x) ∧
    (∀ γ ∈ mirU E (m + 1) m, ∀ g, GlobalTheory.ZUnf.wt N x (ratGL E (m + 1) γ * g) = GlobalTheory.ZUnf.wt N x g) ∧
    ∀ (k : ℕ) (y : UnipotentBlockColumnIndex (m + 1) k k → Ad E) (g : GA E (m + 1)), GlobalTheory.ZUnf.wt N x (blkU y * g) = GlobalTheory.ZUnf.wt N x g := by
  intro E _ _ _ m N x
  refine ⟨measurable_wt N x, fun γ hγ g => ?_, fun k y g => ?_⟩
  · refine wt_of_lastRow_of_detPow (lastRow_mul_of_mem (map_mem_mirU _ hγ) g) ?_
    rw [GlobalTheory.RSJ.Model.detPow_mul, GlobalTheory.RSJ.Model.detPow_ratGL, one_mul]
  · refine wt_of_lastRow_of_detPow (lastRow_mul_of_mem (blkU_mem_mirU m y) g) ?_
    rw [GlobalTheory.RSJ.Model.detPow_mul, detPow_blkU, one_mul]

end GlobalTheory.ZUnfWt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LastRowCongruenceDetWeightMeasurableInvariantStatement
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.RSJ GlobalTheory.MirTower GlobalTheory.CuspGeneric Formalism.L2.Host
open scoped ENNReal NNReal ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastRowCongruenceDetWeight_measurable_invariant : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m N : ℕ) (x : ℝ),
    Measurable (GlobalTheory.ZUnf.wt (E := E) (m := m) N x) ∧
    (∀ γ ∈ mirU E (m + 1) m, ∀ g, GlobalTheory.ZUnf.wt N x (ratGL E (m + 1) γ * g) = GlobalTheory.ZUnf.wt N x g) ∧
    ∀ (k : ℕ) (y : UnipotentBlockColumnIndex (m + 1) k k → Ad E) (g : GA E (m + 1)), GlobalTheory.ZUnf.wt N x (blkU y * g) = GlobalTheory.ZUnf.wt N x g := by
  first | exact @GlobalTheory.ZUnfWt.wt_measurable_invariant | exact GlobalTheory.ZUnfWt.wt_measurable_invariant | (intros; apply GlobalTheory.ZUnfWt.wt_measurable_invariant; all_goals assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodSmoothDecayModerateGrowthRightTranslate
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodSmoothDecayModerateGrowthRightTranslate
open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped Pointwise

noncomputable section

namespace GlobalTheory.RtGood

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

def conjL (y : GL (Fin a) (Cinf E)) (X : Lie E a) : Lie E a := toL ((y⁻¹).val * Matrix.of X * y.val)

theorem lie_mul_rt (y : GL (Fin a) (Cinf E)) (k : GL (Fin a) (Af E)) (X : Lie E a) :
    lie E a X * rt E a (infGL E a y * finGL E a k) = rt E a (infGL E a y * finGL E a k) * lie E a (conjL y X) := by
  have h1 := GlobalTheory.CapAdInv.rt_lie y ((y⁻¹).val * Matrix.of X * y.val)
  have e : toL (y.val * ((y⁻¹).val * Matrix.of X * y.val) * (y⁻¹).val) = X := by
    simp [mul_assoc]
  rw [e] at h1
  have h2 := lie_rt_fin (conjL y X) k
  have h1' : lie E a X * rt E a (infGL E a y) = rt E a (infGL E a y) * lie E a (conjL y X) := h1.symm
  calc lie E a X * rt E a (infGL E a y * finGL E a k)
      = lie E a X * rt E a (infGL E a y) * rt E a (finGL E a k) := by rw [map_mul, mul_assoc]
    _ = rt E a (infGL E a y) * (lie E a (conjL y X) * rt E a (finGL E a k)) := by rw [h1', mul_assoc]
    _ = rt E a (infGL E a y * finGL E a k) * lie E a (conjL y X) := by rw [h2, map_mul, mul_assoc]

theorem word_rt (y : GL (Fin a) (Cinf E)) (k : GL (Fin a) (Af E)) (l : List (Lie E a)) (φ : Sm E a) :
    GlobalTheory.GLFin.word l (rt E a (infGL E a y * finGL E a k) φ) =
      rt E a (infGL E a y * finGL E a k) (GlobalTheory.GLFin.word (l.map (conjL y)) φ) := by
  induction l with
  | nil => rfl
  | cons X l ih =>
    rw [List.map_cons, GlobalTheory.MSpanDecay.word_cons, GlobalTheory.MSpanDecay.word_cons, ih, ← Module.End.mul_apply,
      lie_mul_rt, Module.End.mul_apply]

theorem height_conj_le (y : GL (Fin a) (Cinf E)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u : GL (Fin a) (Cinf E), height (y⁻¹ * u * y) ≤ K * height u := by
  set M : ℝ := ‖rmul (toL y.val)‖ * ‖lmul (toL (y⁻¹).val)‖ with hM
  have hM0 : 0 ≤ M := by positivity
  have key : ∀ u : GL (Fin a) (Cinf E), ‖toL (y⁻¹ * u * y).val‖ ≤ M * ‖toL u.val‖ := by
    intro u
    have e : toL (y⁻¹ * u * y).val = rmul (toL y.val) (lmul (toL (y⁻¹).val) (toL u.val)) := rfl
    rw [e, hM, mul_assoc]
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _))
  refine ⟨1 + M, by positivity, fun u => ?_⟩
  have hi : (y⁻¹ * u * y)⁻¹ = y⁻¹ * u⁻¹ * y := by group
  have k1 := key u
  have k2 := key u⁻¹
  have n1 := norm_nonneg (toL u.val)
  have n2 := norm_nonneg (toL (u⁻¹).val)
  unfold height
  rw [hi]
  nlinarith

theorem decays_rt {G : GA E a → ℂ} (hG : GlobalTheory.ShortVecDecay.Decays G) (h : GA E a) :
    GlobalTheory.ShortVecDecay.Decays (fun g => G (g * h)) := fun L hL C₀ hC₀ N => by
  obtain ⟨C, hC⟩ := hG L hL (C₀ * {h}) (hC₀.mul isCompact_singleton) N
  refine ⟨C, fun g c hc ξ hξ hm => ?_⟩
  have := hC g (c * h) (Set.mul_mem_mul hc (Set.mem_singleton h)) ξ hξ hm
  show ‖G (g * c * h)‖ ≤ _
  rw [mul_assoc]
  exact this

theorem growth_rt {G : GA E a → ℂ} (hG : GlobalTheory.MSpanDecay.Growth G) (h : GA E a) :
    GlobalTheory.MSpanDecay.Growth (fun g => G (g * h)) := by
  obtain ⟨y, k, rfl⟩ : ∃ y k, infGL E a y * finGL E a k = h := ⟨_, _, infGL_mul_finGL h⟩
  obtain ⟨K, hK0, hK⟩ := height_conj_le y
  intro g
  obtain ⟨C, N, hC⟩ := hG (g * (infGL E a y * finGL E a k))
  refine ⟨|C| * K ^ N, N, fun u => ?_⟩
  have hz : y * (y⁻¹ * u * y) = u * y := by group
  have e : g * infGL E a u * (infGL E a y * finGL E a k) =
      g * (infGL E a y * finGL E a k) * infGL E a (y⁻¹ * u * y) := by
    rw [mul_assoc g (infGL E a y * finGL E a k), mul_assoc (infGL E a y), ← infGL_comm (y⁻¹ * u * y) k,
      ← mul_assoc (infGL E a y), ← map_mul, hz, map_mul]
    simp only [mul_assoc]
  show ‖G (g * infGL E a u * (infGL E a y * finGL E a k))‖ ≤ _
  rw [e]
  have h1 := one_le_height u
  have h2 := hK u
  have h3 : 0 ≤ height (y⁻¹ * u * y) := (zero_le_one.trans (one_le_height _))
  calc _ ≤ C * height (y⁻¹ * u * y) ^ N := hC _
    _ ≤ |C| * height (y⁻¹ * u * y) ^ N := mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg h3 N)
    _ ≤ |C| * (K * height u) ^ N := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h3 h2 N) (abs_nonneg C)
    _ = |C| * K ^ N * height u ^ N := by rw [mul_pow, mul_assoc]

theorem good_mul_right : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (F : GA E a → ℂ)
    (h : GA E a), GlobalTheory.MSpanDecay.Good F → GlobalTheory.MSpanDecay.Good (fun g => F (g * h)) := by
  intro E _ _ _ a F h hF
  obtain ⟨y, k, rfl⟩ : ∃ y k, infGL E a y * finGL E a k = h := ⟨_, _, infGL_mul_finGL h⟩
  obtain ⟨hS, hl⟩ := hF
  refine ⟨rt_mem_Sm _ F hS, fun l => ?_⟩
  have e : (⟨fun g => F (g * (infGL E a y * finGL E a k)), rt_mem_Sm _ F hS⟩ : Sm E a) =
      rt E a (infGL E a y * finGL E a k) ⟨F, hS⟩ := rfl
  rw [e, word_rt]
  obtain ⟨hd, hg⟩ := hl (l.map (conjL y))
  exact ⟨decays_rt hd _, growth_rt hg _⟩

end GlobalTheory.RtGood

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodSmoothDecayModerateGrowthRightTranslateStatement
open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodSmoothDecayModerateGrowth_rightTranslate : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (F : GA E a → ℂ) (h : GA E a), GlobalTheory.MSpanDecay.Good F → GlobalTheory.MSpanDecay.Good (fun g => F (g * h)) := by
  first | exact @GlobalTheory.RtGood.good_mul_right | exact GlobalTheory.RtGood.good_mul_right | (intros; apply GlobalTheory.RtGood.good_mul_right <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlobalWhittakerCoeffEqIteratedColumnTransform
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlobalWhittakerCoeffEqIteratedColumnTransform
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.RSJ GlobalTheory.MirTower GlobalTheory.CuspGeneric Formalism.L2.Host
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace GlobalTheory.WhitCols

open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker

variable {E : Type} [Field E] [NumberField E]

theorem avg_eq_setIntegral {ι : Type} [Fintype ι] (Φ : (ι → Ad E) → ℂ) (hΦ : Per (ratV E ι) Φ) :
    avg (ratV E ι) Φ = ∫ x in vecDomain E ι, Φ x ∂vecMeasure E ι := by
  have hF : IsAddFundamentalDomain (ratV E ι) (vecDomain E ι) (vecMeasure E ι) := isAddFundamentalDomain_vecDomain
  obtain ⟨-, -, -, h⟩ := GlobalTheory.CuspGeneric.setIntegral_eq_mass_mul_avg (ι → Ad E) (ratV E ι) (isCoLat_ratV E ι)
    (vecMeasure E ι) (vecDomain E ι) inferInstance hF Φ hΦ
  rw [h, vecMeasure_vecDomain]
  simp

def colIx {a k : ℕ} (hk : k < a) : Fin k ≃ UnipotentBlockColumnIndex a k k where
  toFun i := ⟨(⟨i.1, by omega⟩, ⟨k, hk⟩), i.2, le_rfl, le_rfl⟩
  invFun t := ⟨t.1.1.1, t.2.1⟩
  left_inv i := rfl
  right_inv t := by
    obtain ⟨⟨i, j⟩, h1, h2, h3⟩ := t
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Fin.ext
      dsimp only at h1 h2 h3 ⊢
      omega

def colHom {a k : ℕ} (hk : k < a) : (Fin k → Ad E) ≃ₜ+ (UnipotentBlockColumnIndex a k k → Ad E) where
  toFun x := fun t => x ((colIx hk).symm t)
  invFun y := fun i => y (colIx hk i)
  left_inv x := by funext i; simp
  right_inv y := by funext t; simp
  map_add' x y := rfl
  continuous_toFun := continuous_pi fun t => continuous_apply _
  continuous_invFun := continuous_pi fun i => continuous_apply _

theorem colHom_mem_iff {a k : ℕ} (hk : k < a) (x : Fin k → Ad E) :
    colHom hk x ∈ ratV E (UnipotentBlockColumnIndex a k k) ↔ x ∈ ratV E (Fin k) := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨fun i => c (colIx hk i), funext fun i => ?_⟩
    have := congrFun hc (colIx hk i)
    simpa [colHom] using this
  · rintro ⟨c, rfl⟩
    exact ⟨fun t => c ((colIx hk).symm t), rfl⟩

theorem blkU_colHom {a k : ℕ} (hk : k < a) (x : Fin k → Ad E) :
    (blkU (colHom hk x) : GL (Fin a) (Ad E)) = colGL k x := by
  refine Units.ext ?_
  ext i j
  rw [blkU_apply]
  simp only [colGL, coe_uGL, uMat_apply, colX_apply, Matrix.one_apply, colHom, colIx]
  split_ifs <;> first | rfl | simp_all
  all_goals (exfalso; simp only [Fin.ext_iff, Fin.lt_def, Fin.le_def] at *; omega)

theorem dot_colHom {a k : ℕ} (hk : k < a) (x : Fin k → Ad E) :
    dot (eLast a k) (colHom hk x) = pair (lastVec k) x := by
  rw [dot, pair, ← (colIx hk).sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [colHom, eLast, lastVec, colIx, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk]
  by_cases h : (i : ℕ) + 1 = k <;> simp [h]

theorem colT_eq_stepCoeff {a k : ℕ} (hk : k < a) {F : GA E a → ℂ} (hc : Continuous F)
    (hl : ∀ (ξ : Fin k → E) g, F (AdelicGLn.diagonal E a (colGL k ξ) * g) = F g) (g : GA E a) :
    colT (GlobalTheory.StdCharConductor.psi E) k F g = stepCoeff k F g := by
  have hψ := GlobalTheory.StdCharConductor.stdPsi_psi E
  have hl' : ∀ (c : UnipotentBlockColumnIndex a k k → E) g, F (ratGL E a (blkU c) * g) = F g := by
    intro c g
    have e : ratGL E a (blkU c) = AdelicGLn.diagonal E a (colGL k (fun i => c (colIx hk i))) := by
      rw [ratGL_blkU, diagonal_colGL, ← blkU_colHom hk]
      congr 1
      funext t
      simp [colHom]
    rw [e, hl]
  have hP := per_coef hψ (eLast a k) hc hl' g
  have hP' : Per (ratV E (Fin k)) (fun x => (fun y : UnipotentBlockColumnIndex a k k → Ad E =>
      GlobalTheory.StdCharConductor.psi E (-dot (eLast a k) y) * F (blkU y * g)) (colHom hk x)) := by
    refine ⟨hP.1.comp (colHom hk).continuous_toFun, fun γ hγ x => ?_⟩
    simp only [map_add (f := _)]
    exact hP.2 _ ((colHom_mem_iff hk γ).2 hγ) _
  unfold colT coefF
  rw [← avg_equiv (Fin k → Ad E) (UnipotentBlockColumnIndex a k k → Ad E) (ratV E (Fin k)) (ratV E (UnipotentBlockColumnIndex a k k)) (isCoLat_ratV E _)
    (isCoLat_ratV E _) (colHom hk) (colHom_mem_iff hk) _ hP, avg_eq_setIntegral _ hP']
  unfold stepCoeff vecCoeff
  refine setIntegral_congr_fun measurableSet_vecDomain fun x _ => ?_
  simp only [blkU_colHom, dot_colHom, GlobalTheory.StdCharConductor.psi_apply]
  ring

def IsUU {j : ℕ} (h : Matrix (Fin j) (Fin j) E) : Prop :=
  ∀ i l : Fin j, l ≤ i → h i l = (1 : Matrix (Fin j) (Fin j) E) i l

theorem IsUU.isLastRowUnit {j : ℕ} {h : Matrix (Fin j) (Fin j) E} (hh : IsUU h) : IsLastRowUnit h := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · funext c; exact c.elim0
  · funext c
    have hc : c ≤ (⟨j - 1, by omega⟩ : Fin j) := by rw [Fin.le_def]; show (c : ℕ) ≤ j - 1; omega
    rw [vecMul_lastVec _ _ hj, hh _ _ hc, Matrix.one_apply]
    simp only [lastVec, Fin.ext_iff]
    split_ifs <;> first | rfl | (exfalso; omega)

omit [NumberField E] in
theorem isUU_blockMat {j : ℕ} {h : Matrix (Fin j) (Fin j) E} (hh : IsUU h) :
    IsUU (blockMat (n := j + 1) (Nat.le_succ j) h) := by
  intro i l hli
  rw [blockMat_apply]
  split_ifs with ha hb
  · rw [hh _ _ (by rw [Fin.le_def] at hli ⊢; exact hli), Matrix.one_apply, Matrix.one_apply]
    simp only [Fin.ext_iff]
  · exfalso; rw [Fin.le_def] at hli; omega
  all_goals simp_all [Matrix.one_apply]

omit [NumberField E] in
theorem isUU_colX {j : ℕ} (ξ : Fin j → E) : IsUU (uMat (colX (n := j + 1) j ξ)) := by
  intro i l hli
  rw [uMat_apply, Matrix.one_apply]
  split_ifs <;> first | rfl | (exfalso; simp only [Fin.lt_def, Fin.le_def] at *; omega)

theorem partialCoeff_uu {n : ℕ} {f : GA E n → ℂ}
    (hf : ∀ γ ∈ mirU E n 0, ∀ g, f (ratGL E n γ * g) = f g) :
    ∀ (m j : ℕ), n - j = m → ∀ (hj : j ≤ n) (h : GL (Fin j) E), IsUU (h : Matrix (Fin j) (Fin j) E) → ∀ g,
      partialCoeff f j (AdelicGLn.diagonal E n (blockGL hj h) * g) = partialCoeff f j g := by
  intro m
  induction m with
  | zero =>
    intro j hjm hj h hh g
    obtain rfl : j = n := by omega
    rw [partialCoeff_self]
    have : blockGL hj h = h := Units.ext (by rw [coe_blockGL]; exact blockMat_self _)
    rw [this]
    exact hf h (mem_mirU.2 fun i k _ hk => hh i k hk) g
  | succ m ih =>
    intro j hjm hj h hh g
    have hjn : j < n := by omega
    rw [partialCoeff_of_lt f hjn]
    have hB : ∀ g, partialCoeff f (j + 1) (AdelicGLn.diagonal E n (blockGL hjn.le h) * g) =
        partialCoeff f (j + 1) g := by
      intro g
      rw [← blockGL_blockGL (Nat.le_succ j) hjn]
      exact ih (j + 1) (by omega) hjn _ (isUU_blockMat hh) g
    have hC : ∀ (ξ : Fin j → E) g, partialCoeff f (j + 1) (AdelicGLn.diagonal E n (colGL j ξ) * g) =
        partialCoeff f (j + 1) g := by
      intro ξ g
      rw [colGL_eq_blockGL (Nat.lt_succ_self j) hjn]
      exact ih (j + 1) (by omega) hjn _ (isUU_colX _) g
    rw [stepCoeff_diagonal_blockGL hjn h hB hC g, hh.isLastRowUnit]
    rfl

theorem colT_partialCoeff {m : ℕ} {f : GA E (m + 1) → ℂ} (hc : Continuous f)
    (hf : ∀ γ ∈ mirU E (m + 1) 0, ∀ g, f (ratGL E (m + 1) γ * g) = f g) {k : ℕ} (hk : k < m + 1) :
    colT (GlobalTheory.StdCharConductor.psi E) k (partialCoeff f (k + 1)) = partialCoeff f k := by
  funext g
  rw [partialCoeff_of_lt f hk]
  refine colT_eq_stepCoeff hk (continuous_partialCoeff hc _) (fun ξ g => ?_) g
  rw [colGL_eq_blockGL (Nat.lt_succ_self k) hk]
  exact partialCoeff_uu hf _ (k + 1) rfl hk _ (isUU_colX _) g

theorem whit_partialCoeff {m : ℕ} {f : GA E (m + 1) → ℂ} (hc : Continuous f)
    (hf : ∀ γ ∈ mirU E (m + 1) 0, ∀ g, f (ratGL E (m + 1) γ * g) = f g) :
    ∀ i, i ≤ m → GlobalTheory.CuspGeneric.whit (GlobalTheory.StdCharConductor.psi E) i (partialCoeff f (i + 1)) = partialCoeff f 1
  | 0, _ => rfl
  | i + 1, hi => by
    rw [GlobalTheory.CuspGeneric.whit_succ, colT_partialCoeff hc hf (by omega : i + 1 < m + 1),
      whit_partialCoeff hc hf i (by omega)]

theorem whit_eq_colWhit : ∀ (E : Type) [Field E] [NumberField E] (m : ℕ) (f : GA E (m + 1) → ℂ), Continuous f →
    (∀ γ ∈ mirU E (m + 1) 0, ∀ g, f (ratGL E (m + 1) γ * g) = f g) →
    ∀ g, GlobalTheory.JSW.whit f g = GlobalTheory.CuspGeneric.whit (GlobalTheory.StdCharConductor.psi E) m f g := by
  intro E _ _ m f hc hf g
  rw [GlobalTheory.JSW.whit, whittaker_eq_partialCoeff hc (Nat.succ_pos m), ← whit_partialCoeff hc hf m le_rfl,
    partialCoeff_self]

end GlobalTheory.WhitCols
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlobalWhittakerCoeffEqIteratedColumnTransformStatement
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.RSJ GlobalTheory.MirTower GlobalTheory.CuspGeneric Formalism.L2.Host
open scoped ENNReal NNReal ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.globalWhittakerCoeff_eq_iteratedColumnTransform : ∀ (E : Type) [Field E] [NumberField E] (m : ℕ) (f : GA E (m + 1) → ℂ), Continuous f →
    (∀ γ ∈ mirU E (m + 1) 0, ∀ g, f (ratGL E (m + 1) γ * g) = f g) →
    ∀ g, GlobalTheory.JSW.whit f g = GlobalTheory.CuspGeneric.whit (GlobalTheory.StdCharConductor.psi E) m f g := by
  first | exact @GlobalTheory.WhitCols.whit_eq_colWhit | exact GlobalTheory.WhitCols.whit_eq_colWhit | (intros; apply GlobalTheory.WhitCols.whit_eq_colWhit; all_goals assumption)
end
end
