module

public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIdealInClassOfNormLeSqrtDiscr
public import Formalism.SatakeDualWeyl.Statement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IntegralNormSqLp
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LogAddRpowMulLogPowLeRpow
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormOneSubConjMul
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.InvariantRadonFibre
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NegSumLogDerivNonneg

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ClassNumberLeAbsDiscrOfFinrankEqTwo
open Complex DirichletCharacter ArithmeticFunction MeasureTheory

namespace GlobalTheory

theorem _root_.GlobalTheory.classNumber_le_abs_discr_of_finrank_eq_two (K : Type) [Field K] [NumberField K]
    (h : Module.finrank ℚ K = 2) :
    (NumberField.classNumber K : ℝ) ≤ |(NumberField.discr K : ℝ)| := by
  have hb := _root_.GlobalTheory.classNumber_le_sqrt_discr_mul_pow_pred K
  rw [h] at hb
  norm_num at hb
  have hs := _root_.GlobalTheory.one_le_sqrt_abs_discr K
  set s := √|(NumberField.discr K : ℝ)| with hs_def
  have hlog : Real.log s ≤ s - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have hsq : s * s = |(NumberField.discr K : ℝ)| :=
    Real.mul_self_sqrt (abs_nonneg _)
  calc (NumberField.classNumber K : ℝ) ≤ s * (1 + Real.log s) := hb
    _ ≤ s * s := by apply mul_le_mul_of_nonneg_left _ (by linarith); linarith
    _ = |(NumberField.discr K : ℝ)| := hsq

theorem _root_.GlobalTheory.classNumber_le_four_mul_abs_discr :
    ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 →
      (NumberField.classNumber K : ℝ) ≤ 4 * |(NumberField.discr K : ℝ)| := by
  intro K _ _ h
  have := _root_.GlobalTheory.classNumber_le_abs_discr_of_finrank_eq_two K h
  have := abs_nonneg (NumberField.discr K : ℝ)
  linarith

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DualOfDualFrames
open Matrix Formalism.UG

namespace GlobalTheory.DualFrames

variable {A : Type} [CommRing A] {k : ℕ}

theorem hform_eq_dot (τ : A →+* A) (J : Matrix (Fin k) (Fin k) A) (x y : Fin k → A) :
    hform τ J x y = (τ ∘ x) ⬝ᵥ (J *ᵥ y) := by
  unfold hform
  simp [dotProduct, mulVec, Finset.mul_sum, mul_assoc]

theorem hform_frames (τ : A →+* A) (J B C : Matrix (Fin k) (Fin k) A)
    (h : cT τ B * J * C = 1) (x y : Fin k → A) :
    hform τ J (B *ᵥ x) (C *ᵥ y) = ∑ i, τ (x i) * y i := by
  rw [hform_eq_dot]
  have hmap : (τ ∘ (B *ᵥ x)) = (B.map τ) *ᵥ (τ ∘ x) := by
    funext i
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
  have hct : (B.map τ)ᵀ = cT τ B := by
    unfold cT
    rfl
  rw [hmap, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, hct, h, Matrix.one_mulVec]
  simp [dotProduct]

theorem hform_swap (τ : A →+* A) (hτ : ∀ a, τ (τ a) = a) (J : Matrix (Fin k) (Fin k) A)
    (hJ : IsHerm τ J) (x y : Fin k → A) : τ (hform τ J x y) = hform τ J y x := by
  unfold IsHerm cT at hJ
  have hJ' : ∀ i j, τ (J i j) = J j i := by
    intro i j
    simpa using congrFun (congrFun hJ j) i
  unfold hform
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, hτ, hJ']
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem exists_mulVec (B : GL (Fin k) A) (y : Fin k → A) :
    ∃ z, (B : Matrix (Fin k) (Fin k) A) *ᵥ z = y := by
  refine ⟨((B⁻¹ : GL (Fin k) A) : Matrix (Fin k) (Fin k) A) *ᵥ y, ?_⟩
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

theorem dual_of_dual_frames :
    ∀ (A : Type) [CommRing A] (S : Subring A) (τ : A →+* A), (∀ a, τ (τ a) = a) →
      (∀ a ∈ S, τ a ∈ S) → ∀ (k : ℕ) (J : Matrix (Fin k) (Fin k) A), IsHerm τ J →
      ∀ (B C : GL (Fin k) A) (L₁ L₂ : Submodule S (Fin k → A)),
      cT τ (B : Matrix (Fin k) (Fin k) A) * J * (C : Matrix (Fin k) (Fin k) A) = 1 →
      (∀ y : Fin k → A, (B : Matrix (Fin k) (Fin k) A) *ᵥ y ∈ L₁ ↔ ∀ i, y i ∈ S) →
      (∀ y : Fin k → A, (C : Matrix (Fin k) (Fin k) A) *ᵥ y ∈ L₂ ↔ ∀ i, y i ∈ S) →
      (∀ y, y ∈ L₂ ↔ ∀ x ∈ L₁, hform τ J x y ∈ S) ∧
      (∀ y, y ∈ L₁ ↔ ∀ x ∈ L₂, hform τ J x y ∈ S) ∧
      (∀ x, x ∈ L₁ ↔ ∀ y ∈ L₂, hform τ J x y ∈ S) := by
  intro A _ S τ hτ hS k J hJ B C L₁ L₂ h hL₁ hL₂

  have pair : ∀ u v : Fin k → A,
      hform τ J ((B : Matrix (Fin k) (Fin k) A) *ᵥ u) ((C : Matrix (Fin k) (Fin k) A) *ᵥ v) =
        ∑ i, τ (u i) * v i :=
    fun u v => hform_frames τ J B C h u v
  have flip : ∀ x y, hform τ J x y = τ (hform τ J y x) :=
    fun x y => (hform_swap τ hτ J hJ y x).symm
  have memS_iff : ∀ a, τ a ∈ S ↔ a ∈ S := fun a =>
    ⟨fun ha => hτ a ▸ hS _ ha, hS a⟩
  have single_mem : ∀ i j, (Pi.single i (1 : A) : Fin k → A) j ∈ S := by
    intro i j
    by_cases hj : j = i
    · subst hj
      simp
    · simp [hj, S.zero_mem]
  have coord : ∀ u v : Fin k → A, (∀ i, u i ∈ S) → (∀ i, v i ∈ S) → ∑ i, τ (u i) * v i ∈ S :=
    fun u v hu hv => sum_mem fun i _ => mul_mem (hS _ (hu i)) (hv i)
  have part1 : ∀ y, y ∈ L₂ ↔ ∀ x ∈ L₁, hform τ J x y ∈ S := by
    intro y
    obtain ⟨v, rfl⟩ := exists_mulVec C y
    rw [hL₂]
    constructor
    · intro hv x hx
      obtain ⟨u, rfl⟩ := exists_mulVec B x
      rw [pair]
      exact coord u v ((hL₁ u).1 hx) hv
    · intro hall i
      have key := hall ((B : Matrix (Fin k) (Fin k) A) *ᵥ Pi.single i 1) ((hL₁ _).2 (single_mem i))
      have e : ∑ j, τ ((Pi.single i (1 : A) : Fin k → A) j) * v j = v i := by
        simp [Pi.single_apply]
      rwa [pair, e] at key
  have part2 : ∀ y, y ∈ L₁ ↔ ∀ x ∈ L₂, hform τ J x y ∈ S := by
    intro y
    obtain ⟨v, rfl⟩ := exists_mulVec B y
    rw [hL₁]
    constructor
    · intro hv x hx
      obtain ⟨u, rfl⟩ := exists_mulVec C x
      rw [flip, pair, memS_iff]
      exact coord v u hv ((hL₂ u).1 hx)
    · intro hall i
      have key := hall ((C : Matrix (Fin k) (Fin k) A) *ᵥ Pi.single i 1) ((hL₂ _).2 (single_mem i))
      have e : ∑ j, τ (v j) * (Pi.single i (1 : A) : Fin k → A) j = τ (v i) := by
        simp [Pi.single_apply]
      rwa [flip, pair, memS_iff, e, memS_iff] at key
  have part3 : ∀ x, x ∈ L₁ ↔ ∀ y ∈ L₂, hform τ J x y ∈ S := by
    intro x
    rw [part2]
    refine forall₂_congr fun y _ => ?_
    rw [flip x y, memS_iff]
  exact ⟨part1, part2, part3⟩

end GlobalTheory.DualFrames
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ImportsMore
open Complex DirichletCharacter ArithmeticFunction MeasureTheory

namespace GlobalTheory.ZetaWide

theorem scaled : ∃ C : ℝ, 0 < C ∧ ∀ (F : ℂ → ℂ) (c : ℂ) (M : ℝ), Differentiable ℂ F → F c ≠ 0 →
    (∀ w, ‖w - c‖ ≤ 15/4 → ‖F w‖ ≤ M) →
    ({w : ℂ | ‖w - c‖ ≤ 7/2 ∧ F w = 0}.Finite ∧
      (∑ᶠ w ∈ {w : ℂ | ‖w - c‖ ≤ 7/2 ∧ F w = 0}, (analyticOrderNatAt F w : ℝ))
        ≤ C * (1 + Real.log (M / ‖F c‖))) ∧
    ∀ s : ℂ, ‖s - c‖ ≤ 3 → F s ≠ 0 →
      ‖deriv F s / F s - ∑ᶠ w ∈ {w : ℂ | ‖w - c‖ ≤ 7/2 ∧ F w = 0},
        (analyticOrderNatAt F w : ℂ) / (s - w)‖ ≤ C * (1 + Real.log (M / ‖F c‖)) := by
  obtain ⟨C, hC, H⟩ := GlobalTheory.LogDerivZeros.main (4/5) (14/15) (by norm_num) (by norm_num)
    (by norm_num)
  refine ⟨C, hC, fun F c M hF hc hM => ?_⟩
  set g : ℂ → ℂ := fun z => c + 15/4 * z with hg
  have hgn : ∀ z, ‖g z - c‖ = 15/4 * ‖z‖ := fun z => by simp [hg]
  have hgd : ∀ z, HasDerivAt g (15/4) z := fun z => by
    have := ((hasDerivAt_id z).const_mul (15/4 : ℂ)).const_add c
    rw [mul_one] at this
    exact this
  have hgD : Differentiable ℂ g := fun z => (hgd z).differentiableAt
  have hfD : Differentiable ℂ (F ∘ g) := hF.comp hgD
  have hg0 : g 0 = c := by simp [hg]
  have hf0 : (F ∘ g) 0 = F c := by simp [hg0]
  obtain ⟨⟨h1, h2⟩, h3⟩ := H (F ∘ g) M (fun z _ => hfD.analyticAt z) (by rwa [hf0])
    (fun z hz => hM _ (by
      have : ‖z‖ ≤ 1 := by simpa using hz
      rw [hgn]; linarith))
  rw [hf0] at h2 h3
  have hinj : Function.Injective g := fun a b h => by simpa [hg] using h
  have hsur : ∀ w, g ((w - c) * (4/15)) = w := fun w => by simp only [hg]; ring
  have hset : {w : ℂ | ‖w - c‖ ≤ 7/2 ∧ F w = 0} = g '' {w : ℂ | ‖w‖ ≤ 14/15 ∧ (F ∘ g) w = 0} := by
    ext w
    constructor
    · rintro ⟨ha, hb⟩
      refine ⟨(w - c) * (4/15), ⟨?_, by simp only [Function.comp, hsur, hb]⟩, hsur w⟩
      have := hgn ((w - c) * (4/15))
      rw [hsur] at this
      linarith
    · rintro ⟨z, ⟨ha, hb⟩, rfl⟩
      exact ⟨by rw [hgn]; linarith, hb⟩
  have hord : ∀ z, analyticOrderNatAt (F ∘ g) z = analyticOrderNatAt F (g z) := fun z => by
    unfold analyticOrderNatAt
    rw [analyticOrderAt_comp_of_deriv_ne_zero (hgD.analyticAt z) (by rw [(hgd z).deriv]; norm_num)]
  simp only [hord] at h2 h3
  rw [hset]
  refine ⟨⟨h1.image g, by rwa [finsum_mem_image hinj.injOn]⟩, fun s hs hFs => ?_⟩
  obtain ⟨z, rfl⟩ : ∃ z, s = g z := ⟨_, (hsur s).symm⟩
  rw [hgn] at hs
  have h4 := h3 z (by linarith) hFs
  have hL : 0 ≤ C * (1 + Real.log (M / ‖F c‖)) := (norm_nonneg _).trans h4
  rw [finsum_mem_image hinj.injOn]
  rw [finsum_mem_eq_finite_toFinset_sum _ h1] at h4 ⊢
  have hd : deriv (F ∘ g) z = deriv F (g z) * (15/4) :=
    ((hF (g z)).hasDerivAt.comp z (hgd z)).deriv
  have e : deriv F (g z) / F (g z) - ∑ w ∈ h1.toFinset, (analyticOrderNatAt F (g w) : ℂ) / (g z - g w)
      = (4/15) * (deriv (F ∘ g) z / (F ∘ g) z -
        ∑ w ∈ h1.toFinset, (analyticOrderNatAt F (g w) : ℂ) / (z - w)) := by
    rw [hd, mul_sub, Finset.mul_sum]
    congr 1
    · simp only [Function.comp]; ring
    · refine Finset.sum_congr rfl fun w _ => ?_
      have : g z - g w = 15/4 * (z - w) := by simp only [hg]; ring
      rw [this, div_eq_mul_inv, mul_inv]
      ring
  rw [e, norm_mul]
  have : ‖(4/15 : ℂ)‖ = 4/15 := by simp
  rw [this]
  linarith

theorem zeta₁_eq {s : ℂ} (hs : s ≠ 1) : riemannZeta₁ s = (s - 1) * riemannZeta s := by
  rw [riemannZeta_eq_inv_sub_mul hs, mul_inv_cancel_left₀ (sub_ne_zero.2 hs)]

theorem order_zeta₁_eq {s : ℂ} (hs : s ≠ 1) :
    analyticOrderNatAt riemannZeta₁ s = analyticOrderNatAt riemannZeta s := by
  unfold analyticOrderNatAt
  have hev : riemannZeta₁ =ᶠ[nhds s] (fun z => z - 1) * riemannZeta := by
    filter_upwards [isOpen_ne.mem_nhds hs] with z hz
    exact zeta₁_eq hz
  have h1 : AnalyticAt ℂ (fun z : ℂ => z - 1) s := by fun_prop
  have h2 : AnalyticAt ℂ riemannZeta s := analyticOn_riemannZeta s hs
  rw [analyticOrderAt_congr hev, analyticOrderAt_mul h1 h2,
    h1.analyticOrderAt_eq_zero.2 (sub_ne_zero.2 hs), zero_add]

theorem main : ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, -1 ≤ s.re → s.re ≤ 2 → s ≠ 1 → riemannZeta s ≠ 0 → {w : ℂ | ‖w - (2 + s.im * I)‖ ≤ 7/2 ∧ w ≠ 1 ∧ riemannZeta w = 0}.Finite ∧ (∑ᶠ w ∈ {w : ℂ | ‖w - (2 + s.im * I)‖ ≤ 7/2 ∧ w ≠ 1 ∧ riemannZeta w = 0}, (analyticOrderNatAt riemannZeta w : ℝ)) ≤ C * Real.log (|s.im| + 2) ∧ ‖deriv riemannZeta s / riemannZeta s + 1 / (s - 1) - ∑ᶠ w ∈ {w : ℂ | ‖w - (2 + s.im * I)‖ ≤ 7/2 ∧ w ≠ 1 ∧ riemannZeta w = 0}, (analyticOrderNatAt riemannZeta w : ℂ) / (s - w)‖ ≤ C * Real.log (|s.im| + 2) := by
  obtain ⟨C, hC, H⟩ := scaled
  obtain ⟨B, hB, hBl⟩ := GlobalTheory.ZetaLeft.norm_sub_one_mul_riemannZeta_le
  set K : ℝ := 2 * (B + 1) * 4 ^ 5 with hK
  have hK1 : 1 ≤ K := by rw [hK]; linarith
  have hlK : 0 ≤ Real.log K := Real.log_nonneg hK1
  refine ⟨C * (2 * (1 + Real.log K) + 5), by positivity, fun s hs1 hs2 hs hz => ?_⟩
  set c : ℂ := 2 + s.im * I with hc
  set T : ℝ := |s.im| + 2 with hT
  have hT2 : 2 ≤ T := by have := abs_nonneg s.im; linarith
  have hcre : c.re = 2 := by simp [hc]
  have hc1 : c ≠ 1 := fun h => by rw [h] at hcre; norm_num at hcre
  have hcn : ‖c‖ ≤ T := by
    refine (norm_add_le _ _).trans ?_
    simp [hT, add_comm]
  have hlow : 1 / 2 ≤ ‖riemannZeta₁ c‖ := by
    have h := GlobalTheory.LLower.norm_LFunction_ge 1 1 c (by rw [hcre]; norm_num)
    rw [LFunction_modOne_eq, hcre] at h
    have h' : 1 ≤ ‖c - 1‖ := by
      have := Complex.re_le_norm (c - 1)
      rw [sub_re, hcre, one_re] at this
      linarith
    rw [zeta₁_eq hc1, norm_mul]
    nlinarith
  have hne : riemannZeta₁ c ≠ 0 := norm_pos_iff.1 (by linarith)
  have hup : ∀ w, ‖w - c‖ ≤ 15/4 → ‖riemannZeta₁ w‖ ≤ (B + 1) * (4 * T) ^ 5 := by
    intro w hw
    have hp : 1 ≤ (4 * T) ^ 5 := one_le_pow₀ (by linarith)
    by_cases h1 : w = 1
    · rw [h1, riemannZeta₁_one, norm_one]
      nlinarith
    · have hre : -(7/4 : ℝ) ≤ w.re := by
        have := Complex.abs_re_le_norm (w - c)
        rw [sub_re, hcre] at this
        have := neg_abs_le (w.re - 2)
        linarith
      have hwn : ‖w‖ + 2 ≤ 4 * T := by
        have := norm_add_le (w - c) c
        rw [sub_add_cancel] at this
        linarith
      rw [zeta₁_eq h1]
      refine (hBl w hre h1).trans ?_
      gcongr
      linarith
  obtain ⟨⟨h1, h2⟩, h3⟩ := H riemannZeta₁ c _ differentiable_riemannZeta₁ hne hup
  have hbound : C * (1 + Real.log ((B + 1) * (4 * T) ^ 5 / ‖riemannZeta₁ c‖))
      ≤ C * (2 * (1 + Real.log K) + 5) * Real.log T := by
    have hlT : 1 / 2 ≤ Real.log T := by
      have := Real.log_two_gt_d9
      have := Real.log_le_log (by norm_num) hT2
      linarith
    have ha : (B + 1) * (4 * T) ^ 5 / ‖riemannZeta₁ c‖ ≤ K * T ^ 5 := by
      calc _ ≤ (B + 1) * (4 * T) ^ 5 / (1 / 2) := by gcongr
        _ = K * T ^ 5 := by rw [hK]; ring
    have hb := Real.log_le_log (by positivity) ha
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow] at hb
    rw [mul_assoc]
    gcongr
    push_cast at hb
    nlinarith
  have hset : {w : ℂ | ‖w - c‖ ≤ 7/2 ∧ w ≠ 1 ∧ riemannZeta w = 0}
      = {w : ℂ | ‖w - c‖ ≤ 7/2 ∧ riemannZeta₁ w = 0} := by
    ext w
    by_cases hw : w = 1
    · simp [hw]
    · simp [hw, zeta₁_eq hw, sub_ne_zero.2 hw]
  have hne1 : ∀ w ∈ {w : ℂ | ‖w - c‖ ≤ 7/2 ∧ riemannZeta₁ w = 0}, w ≠ 1 := by
    rintro w ⟨_, hw⟩ rfl
    simp at hw
  have hs0 : s - 1 ≠ 0 := sub_ne_zero.2 hs
  rw [hset]
  refine ⟨h1, ?_, ?_⟩
  · refine le_trans (le_of_eq ?_) (h2.trans hbound)
    exact finsum_mem_congr rfl fun w hw => by rw [order_zeta₁_eq (hne1 w hw)]
  · have hsc : ‖s - c‖ ≤ 3 := by
      have : s - c = ((s.re - 2 : ℝ) : ℂ) := by
        apply Complex.ext <;> simp [hc]
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_le]
      constructor <;> linarith
    have hz1 : riemannZeta₁ s ≠ 0 := by rw [zeta₁_eq hs]; exact mul_ne_zero hs0 hz
    refine le_trans (le_of_eq ?_) ((h3 s hsc hz1).trans hbound)
    congr 2
    · rw [deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add hs, riemannZeta_eq_inv_sub_mul hs]
      field_simp
      ring
    · exact finsum_mem_congr rfl fun w hw => by rw [order_zeta₁_eq (hne1 w hw)]

end GlobalTheory.ZetaWide
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsUniqueHaarOfInvariantRadonOnCosets
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsUniqueHaarOfInvariantRadonOnCosets
open MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
open scoped ENNReal Pointwise

namespace GlobalTheory.QuotientHaar

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] (H : Subgroup G)

theorem measurable_translate (g : G) : Measurable (fun h : H => g * (h : G)) :=
  (continuous_const.mul continuous_subtype_val).measurable

noncomputable def cosetMeasure (ν : Measure H) [ν.IsMulLeftInvariant] : G ⧸ H → Measure G :=
  Quotient.lift (fun g : G => ν.map (fun h : H => g * (h : G))) (by
    intro a b hab
    have hab' : a⁻¹ * b ∈ H := QuotientGroup.leftRel_apply.mp hab
    have h1 := map_mul_left_eq_self ν (⟨a⁻¹ * b, hab'⟩ : H)
    beta_reduce
    conv_lhs => rw [← h1]
    rw [Measure.map_map (measurable_translate H a) (measurable_const_mul _)]
    congr 1
    funext h
    simp [← mul_assoc])

theorem cosetMeasure_mk (ν : Measure H) [ν.IsMulLeftInvariant] (g : G) :
    cosetMeasure H ν (g : G ⧸ H) = ν.map (fun h : H => g * (h : G)) := rfl

theorem cosetMeasure_apply (ν : Measure H) [ν.IsMulLeftInvariant] (g : G) {s : Set G}
    (hs : MeasurableSet s) :
    cosetMeasure H ν (g : G ⧸ H) s = ν ((fun h : H => g * (h : G)) ⁻¹' s) := by
  rw [cosetMeasure_mk, Measure.map_apply (measurable_translate H g) hs]

theorem lintegral_cosetMeasure (ν : Measure H) [ν.IsMulLeftInvariant] {f : G → ℝ≥0∞}
    (hf : Measurable f) (q : G ⧸ H) :
    ∫⁻ x, f x ∂(cosetMeasure H ν q) = fibreIntegral H ν f q := by
  induction q using QuotientGroup.induction_on with
  | H g => rw [cosetMeasure_mk, lintegral_map hf (measurable_translate H g), fibreIntegral_mk]

variable [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]

omit [LocallyCompactSpace G] [SecondCountableTopology G] in
theorem cosetMeasure_lt_top (hH : IsClosed (H : Set G)) (ν : Measure H) [ν.IsHaarMeasure]
    (q : G ⧸ H) {K : Set G} (hK : IsCompact K) : cosetMeasure H ν q K < ⊤ := by
  induction q using QuotientGroup.induction_on with
  | H g =>
    rw [cosetMeasure_apply H ν g hK.measurableSet]
    have h1 : IsCompact ((fun x : G => g * x) ⁻¹' K) :=
      (Homeomorph.mulLeft g).isCompact_preimage.mpr hK
    exact (hH.isClosedEmbedding_subtypeVal.isCompact_preimage h1).measure_lt_top

theorem measurable_cosetMeasure_open (hH : IsClosed (H : Set G)) (ν : Measure H)
    [ν.IsHaarMeasure] [MeasurableSpace (G ⧸ H)] [BorelSpace (G ⧸ H)] {U : Set G}
    (hU : IsOpen U) : Measurable (fun q : G ⧸ H => cosetMeasure H ν q U) := by
  haveI : LocallyCompactSpace H := hH.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology H := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : IsLocallyFiniteMeasure ν := isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts
  haveI : ν.Regular := inferInstance
  refine measurable_of_Ioi fun c => IsOpen.measurableSet ?_
  rw [← (QuotientGroup.isQuotientMap_mk H).isOpen_preimage, isOpen_iff_mem_nhds]
  intro g hg
  simp only [Set.mem_preimage, Set.mem_Ioi, cosetMeasure_apply H ν g hU.measurableSet] at hg
  have hO : IsOpen ((fun h : H => g * (h : G)) ⁻¹' U) :=
    hU.preimage (continuous_const.mul continuous_subtype_val)
  obtain ⟨K, hKU, hK, hc⟩ := hO.exists_lt_isCompact hg
  have hev : ∀ᶠ x in nhds g, ∀ h ∈ K, x * (h : G) ∈ U := by
    refine hK.eventually_forall_of_forall_eventually fun h hh => ?_
    have hcont : Continuous (fun p : G × H => p.1 * (p.2 : G)) := by fun_prop
    exact hcont.continuousAt.eventually_mem (hU.mem_nhds (hKU hh))
  filter_upwards [hev] with x hx
  simp only [Set.mem_preimage, Set.mem_Ioi, cosetMeasure_apply H ν x hU.measurableSet]
  exact hc.trans_le (measure_mono fun h hh => hx h hh)

theorem measurable_cosetMeasure (hH : IsClosed (H : Set G)) (ν : Measure H)
    [ν.IsHaarMeasure] [MeasurableSpace (G ⧸ H)] [BorelSpace (G ⧸ H)] :
    Measurable (cosetMeasure H ν) := by
  let K := CompactExhaustion.choice G
  have hres : ∀ n, Measurable (fun q => (cosetMeasure H ν q).restrict (interior (K n))) := by
    intro n
    haveI : ∀ q, IsFiniteMeasure ((cosetMeasure H ν q).restrict (interior (K n))) := fun q =>
      isFiniteMeasure_restrict.mpr ((measure_mono interior_subset).trans_lt
        (cosetMeasure_lt_top H hH ν q (K.isCompact n))).ne
    have key : ∀ s : Set G, IsOpen s →
        Measurable fun q => (cosetMeasure H ν q).restrict (interior (K n)) s := by
      intro s hs
      simp only [Measure.restrict_apply hs.measurableSet]
      exact measurable_cosetMeasure_open H hH ν (hs.inter isOpen_interior)
    exact Measurable.measure_of_isPiSystem (S := {s : Set G | IsOpen s})
      BorelSpace.measurable_eq isPiSystem_isOpen key (key _ isOpen_univ)
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  have hmono : Monotone fun n => s ∩ interior (K n) := fun a b hab =>
    Set.inter_subset_inter_right _ (interior_mono (K.subset hab))
  have hun : ⋃ n, s ∩ interior (K n) = s := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_inter_iff]
    refine ⟨fun ⟨_, h, _⟩ => h, fun h => ?_⟩
    obtain ⟨n, hn⟩ := K.exists_mem x
    exact ⟨n + 1, h, K.subset_interior_succ n hn⟩
  have : (fun q => cosetMeasure H ν q s) =
      fun q => ⨆ n, (cosetMeasure H ν q).restrict (interior (K n)) s := by
    funext q
    simp only [Measure.restrict_apply hs]
    rw [← hmono.measure_iUnion, hun]
  rw [this]
  exact Measurable.iSup fun n => (Measure.measurable_coe hs).comp (hres n)

theorem measurable_fibreIntegral (hH : IsClosed (H : Set G)) (ν : Measure H)
    [ν.IsHaarMeasure] [MeasurableSpace (G ⧸ H)] [BorelSpace (G ⧸ H)] {f : G → ℝ≥0∞}
    (hf : Measurable f) : Measurable (fibreIntegral H ν f) := by
  have : fibreIntegral H ν f = fun q => ∫⁻ x, f x ∂(cosetMeasure H ν q) :=
    funext fun q => (lintegral_cosetMeasure H ν hf q).symm
  rw [this]
  exact (Measure.measurable_lintegral hf).comp (measurable_cosetMeasure H hH ν)

theorem quotientFormula_bind (hH : IsClosed (H : Set G)) (ν : Measure H)
    [ν.IsHaarMeasure] [MeasurableSpace (G ⧸ H)] [BorelSpace (G ⧸ H)] (μ : Measure (G ⧸ H)) :
    QuotientFormula H (μ.bind (cosetMeasure H ν)) ν μ := by
  intro f hf
  refine ⟨measurable_fibreIntegral H hH ν hf, ?_⟩
  rw [Measure.lintegral_bind (measurable_cosetMeasure H hH ν).aemeasurable hf.aemeasurable]
  exact lintegral_congr fun q => lintegral_cosetMeasure H ν hf q

theorem isHaarMeasure_bind (hH : IsClosed (H : Set G)) (ν : Measure H)
    [ν.IsHaarMeasure] [MeasurableSpace (G ⧸ H)] [BorelSpace (G ⧸ H)] (μ : Measure (G ⧸ H))
    (hμ : IsInvariantRadon H μ) : (μ.bind (cosetMeasure H ν)).IsHaarMeasure := by
  haveI := hμ.finiteOnCompacts
  haveI := hμ.invariant
  have hm := measurable_cosetMeasure H hH ν
  haveI hfin : IsFiniteMeasureOnCompacts (μ.bind (cosetMeasure H ν)) := by
    refine ⟨fun K hK => ?_⟩
    rw [Measure.bind_apply hK.measurableSet hm.aemeasurable]
    have hC : ν (Subtype.val ⁻¹' (K⁻¹ * K)) < ⊤ :=
      (hH.isClosedEmbedding_subtypeVal.isCompact_preimage (hK.inv.mul hK)).measure_lt_top
    have hπ : IsCompact ((QuotientGroup.mk : G → G ⧸ H) '' K) :=
      hK.image QuotientGroup.continuous_mk
    have hle : ∀ q, cosetMeasure H ν q K ≤ ((QuotientGroup.mk : G → G ⧸ H) '' K).indicator
        (fun _ => ν (Subtype.val ⁻¹' (K⁻¹ * K))) q := by
      intro q
      by_cases hq : q ∈ (QuotientGroup.mk : G → G ⧸ H) '' K
      · rw [Set.indicator_of_mem hq]
        obtain ⟨k, hk, rfl⟩ := hq
        rw [cosetMeasure_apply H ν k hK.measurableSet]
        refine measure_mono fun h hh => ?_
        exact ⟨k⁻¹, Set.inv_mem_inv.mpr hk, k * h, hh, by simp⟩
      · induction q using QuotientGroup.induction_on with
        | H g =>
          rw [cosetMeasure_apply H ν g hK.measurableSet]
          have : (fun h : H => g * (h : G)) ⁻¹' K = ∅ :=
            Set.eq_empty_of_forall_notMem fun h hh => hq ⟨g * h, hh, by simp⟩
          simp [this]
    refine (lintegral_mono hle).trans_lt ((lintegral_indicator_const_le _ _).trans_lt ?_)
    exact ENNReal.mul_lt_top hC hπ.measure_lt_top
  haveI hinv : (μ.bind (cosetMeasure H ν)).IsMulLeftInvariant := by
    refine (forall_measure_preimage_mul_iff _).mp fun a s hs => ?_
    rw [Measure.bind_apply hs hm.aemeasurable,
      Measure.bind_apply (measurable_const_mul a hs) hm.aemeasurable]
    have h1 : Measurable fun q => cosetMeasure H ν q s := (Measure.measurable_coe hs).comp hm
    have h2 := (measurePreserving_smul a μ).lintegral_comp h1
    rw [← h2]
    refine lintegral_congr fun q => ?_
    induction q using QuotientGroup.induction_on with
    | H g =>
      change _ = cosetMeasure H ν ((a * g : G) : G ⧸ H) s
      rw [cosetMeasure_apply H ν g (measurable_const_mul a hs), cosetMeasure_apply H ν _ hs]
      congr 1
      ext h
      simp [mul_assoc]
  have hne : μ.bind (cosetMeasure H ν) ≠ 0 := by
    intro h0
    have h1 : μ.bind (cosetMeasure H ν) Set.univ = ν Set.univ * μ Set.univ := by
      rw [Measure.bind_apply MeasurableSet.univ hm.aemeasurable, ← lintegral_const]
      refine lintegral_congr fun q => ?_
      induction q using QuotientGroup.induction_on with
      | H g => rw [cosetMeasure_apply H ν g MeasurableSet.univ, Set.preimage_univ]
    rw [h0] at h1
    exact mul_ne_zero (isOpen_univ.measure_ne_zero ν Set.univ_nonempty)
      (Measure.measure_univ_ne_zero.mpr hμ.ne_zero) h1.symm
  haveI : IsLocallyFiniteMeasure (μ.bind (cosetMeasure H ν)) :=
    isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts
  haveI : NeZero (μ.bind (cosetMeasure H ν)) := ⟨hne⟩
  haveI : (μ.bind (cosetMeasure H ν)).IsOpenPosMeasure :=
    isOpenPosMeasure_of_mulLeftInvariant_of_regular
  exact {}

end GlobalTheory.QuotientHaar

namespace GlobalTheory.QuotientHaar

theorem existsUnique_haar_of_invariantRadon : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (H : Subgroup G) [MeasurableSpace (G ⧸ H)] [BorelSpace (G ⧸ H)], IsClosed (H : Set G) → ∀ (ν : Measure H) [ν.IsHaarMeasure] (μ : Measure (G ⧸ H)), IsInvariantRadon H μ → ∃! dg : Measure G, dg.IsHaarMeasure ∧ QuotientFormula H dg ν μ := by
  intro G _ _ _ _ _ _ _ _ H _ _ hH ν _ μ hμ
  refine ⟨μ.bind (cosetMeasure H ν),
    ⟨isHaarMeasure_bind H hH ν μ hμ, quotientFormula_bind H hH ν μ⟩, fun dg hdg => ?_⟩
  ext s hs
  have hf : Measurable (s.indicator (1 : G → ℝ≥0∞)) := measurable_one.indicator hs
  rw [← lintegral_indicator_one hs, ← lintegral_indicator_one hs, (hdg.2 _ hf).2,
    (quotientFormula_bind H hH ν μ _ hf).2]

end GlobalTheory.QuotientHaar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsUniqueHaarOfInvariantRadonOnCosetsStatement
open MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_haar_of_invariantRadonOnCosets : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (H : Subgroup G) [MeasurableSpace (G ⧸ H)] [BorelSpace (G ⧸ H)], IsClosed (H : Set G) → ∀ (ν : Measure H) [ν.IsHaarMeasure] (μ : Measure (G ⧸ H)), IsInvariantRadon H μ → ∃! dg : Measure G, dg.IsHaarMeasure ∧ QuotientFormula H dg ν μ := by
  first | exact @GlobalTheory.QuotientHaar.existsUnique_haar_of_invariantRadon | exact GlobalTheory.QuotientHaar.existsUnique_haar_of_invariantRadon | (intros; apply GlobalTheory.QuotientHaar.existsUnique_haar_of_invariantRadon <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LogDerivRiemannZetaLocalZeroSum
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LogDerivRiemannZetaLocalZeroSum
open Complex DirichletCharacter ArithmeticFunction MeasureTheory

namespace GlobalTheory.ZetaLocal

lemma zeta₁_eq {s : ℂ} (hs : s ≠ 1) : riemannZeta₁ s = (s - 1) * riemannZeta s := by
  rw [riemannZeta_eq_inv_sub_mul hs, mul_inv_cancel_left₀ (sub_ne_zero.2 hs)]

lemma zeta₁_eq_zero_iff (w : ℂ) : riemannZeta₁ w = 0 ↔ w ≠ 1 ∧ riemannZeta w = 0 := by
  by_cases h : w = 1
  · simp [h]
  · simp [zeta₁_eq h, sub_ne_zero.2 h, h]

lemma order_zeta₁ {w : ℂ} (hw : w ≠ 1) :
    analyticOrderNatAt riemannZeta₁ w = analyticOrderNatAt riemannZeta w := by
  have h1 : riemannZeta₁ =ᶠ[nhds w] (fun s => s - 1) * riemannZeta := by
    filter_upwards [compl_singleton_mem_nhds hw] with s hs using zeta₁_eq hs
  have h2 : AnalyticAt ℂ riemannZeta w :=
    differentiableOn_riemannZeta.analyticAt (compl_singleton_mem_nhds hw)
  have h3 : AnalyticAt ℂ (fun s : ℂ => s - 1) w := by fun_prop
  unfold analyticOrderNatAt
  rw [analyticOrderAt_congr h1, analyticOrderAt_mul h3 h2,
    h3.analyticOrderAt_eq_zero.2 (sub_ne_zero.2 hw), zero_add]

lemma order_shift (c w : ℂ) :
    analyticOrderNatAt (fun z => riemannZeta₁ (c + z)) w
      = analyticOrderNatAt riemannZeta₁ (c + w) := by
  unfold analyticOrderNatAt
  have := analyticOrderAt_comp_of_deriv_ne_zero (f := riemannZeta₁) (g := fun z => c + z)
    (z₀ := w) (by fun_prop) (by simp)
  exact congrArg _ this

lemma logDeriv_zeta₁ {s : ℂ} (hs : s ≠ 1) (h0 : riemannZeta s ≠ 0) :
    deriv riemannZeta₁ s / riemannZeta₁ s = deriv riemannZeta s / riemannZeta s + 1 / (s - 1) := by
  rw [deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add hs, zeta₁_eq hs]
  have := sub_ne_zero.2 hs
  field_simp
  ring

lemma norm_zeta₁_le (t : ℝ) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖riemannZeta₁ (3/2 + t * I + z)‖ ≤ 5 * (|t| + 2) ^ 2 := by
  have ht := abs_nonneg t
  set w : ℂ := 3/2 + t * I + z with hw
  by_cases h : w = 1
  · rw [h, riemannZeta₁_one, norm_one]; nlinarith
  have hre : 1 / 2 ≤ w.re := by
    have := (abs_le.1 ((abs_re_le_norm z).trans hz)).1
    simp [hw]; linarith
  have htI : ‖(t : ℂ) * I‖ = |t| := by simp
  have h1 : ‖w - 1‖ ≤ |t| + 2 := by
    have : w - 1 = 1/2 + t * I + z := by rw [hw]; ring
    rw [this]
    refine norm_add₃_le.trans ?_
    rw [htI]; norm_num; linarith
  have h2 : ‖w‖ ≤ 2 * (|t| + 2) := by
    refine norm_add₃_le.trans ?_
    rw [htI]; norm_num; linarith
  have h3 := GlobalTheory.ZetaHalfPlane.norm_zeta_sub_le w (by linarith) h
  have h4 : ‖w‖ / w.re ≤ 2 * ‖w‖ := by
    rw [div_le_iff₀ (by linarith)]; nlinarith [norm_nonneg w]
  have e : riemannZeta₁ w = (w - 1) * (riemannZeta w - w / (w - 1)) + w := by
    have := sub_ne_zero.2 h
    rw [zeta₁_eq h]; field_simp; ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul]
  have h5 : ‖w - 1‖ * ‖riemannZeta w - w / (w - 1)‖ ≤ (|t| + 2) * (4 * (|t| + 2)) :=
    mul_le_mul h1 (by linarith) (norm_nonneg _) (by linarith)
  nlinarith

lemma le_norm_zeta₁ (t : ℝ) : 1 / 6 ≤ ‖riemannZeta₁ (3/2 + t * I)‖ := by
  set w : ℂ := 3/2 + t * I with hw
  have hre : w.re = 3 / 2 := by simp [hw]
  have h : w ≠ 1 := by
    intro h; rw [h] at hre; norm_num at hre
  have h1 := GlobalTheory.LLower.norm_LFunction_ge 1 (1 : DirichletCharacter ℂ 1) w (by rw [hre]; norm_num)
  rw [LFunction_modOne_eq, hre] at h1
  have h2 : 1 / 2 ≤ ‖w - 1‖ := by
    refine le_trans ?_ (re_le_norm _)
    rw [sub_re, hre]; norm_num
  rw [zeta₁_eq h, norm_mul]
  nlinarith

theorem logDeriv_riemannZeta_local : ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ) (s : ℂ), ‖s - (3/2 + t * I)‖ ≤ 2/3 → s ≠ 1 → riemannZeta s ≠ 0 → {w : ℂ | ‖w - (3/2 + t * I)‖ ≤ 5/6 ∧ w ≠ 1 ∧ riemannZeta w = 0}.Finite ∧ ‖deriv riemannZeta s / riemannZeta s + 1 / (s - 1) - ∑ᶠ w ∈ {w : ℂ | ‖w - (3/2 + t * I)‖ ≤ 5/6 ∧ w ≠ 1 ∧ riemannZeta w = 0}, (analyticOrderNatAt riemannZeta w : ℂ) / (s - w)‖ ≤ C * Real.log (|t| + 2) := by
  obtain ⟨C, hC, H⟩ := GlobalTheory.LogDerivZeros.main (2/3) (5/6) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨9 * C, by positivity, fun t s hs hs1 hs0 => ?_⟩
  have hlow := le_norm_zeta₁ t
  have hup := fun z => norm_zeta₁_le t (z := z)
  set c : ℂ := 3/2 + t * I with hc
  have hd : Differentiable ℂ fun z => riemannZeta₁ (c + z) := by fun_prop
  obtain ⟨⟨hfin, -⟩, H2⟩ := H (fun z => riemannZeta₁ (c + z)) (5 * (|t| + 2) ^ 2)
    (fun z _ => hd.analyticAt z) (by
      simp only [add_zero]
      intro h; rw [h, norm_zero] at hlow; norm_num at hlow)
    (fun z hz => hup z (by simpa using hz))
  have hset : {w : ℂ | ‖w - c‖ ≤ 5/6 ∧ w ≠ 1 ∧ riemannZeta w = 0}
      = (fun z => c + z) '' {w : ℂ | ‖w‖ ≤ 5/6 ∧ riemannZeta₁ (c + w) = 0} := by
    ext w
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨w - c, ⟨h1, by rw [add_sub_cancel]; exact (zeta₁_eq_zero_iff w).2 h2⟩, by simp⟩
    · rintro ⟨z, ⟨h1, h2⟩, rfl⟩
      exact ⟨by simpa using h1, (zeta₁_eq_zero_iff _).1 h2⟩
  rw [hset]
  refine ⟨hfin.image _, ?_⟩
  have H3 := H2 (s - c) hs (by
    simp only [add_sub_cancel]
    exact fun h => hs0 ((zeta₁_eq_zero_iff s).1 h).2)
  rw [finsum_mem_image (add_right_injective c).injOn, ← logDeriv_zeta₁ hs1 hs0]
  have e : (∑ᶠ w ∈ {w : ℂ | ‖w‖ ≤ 5/6 ∧ riemannZeta₁ (c + w) = 0},
      (analyticOrderNatAt riemannZeta (c + w) : ℂ) / (s - (c + w)))
      = ∑ᶠ w ∈ {w : ℂ | ‖w‖ ≤ 5/6 ∧ riemannZeta₁ (c + w) = 0},
      (analyticOrderNatAt (fun z => riemannZeta₁ (c + z)) w : ℂ) / (s - c - w) := by
    refine finsum_mem_congr rfl fun w hw => ?_
    rw [order_shift, order_zeta₁ ((zeta₁_eq_zero_iff _).1 hw.2).1, sub_sub]
  rw [e]
  rw [deriv_comp_const_add] at H3
  simp only [add_sub_cancel, add_zero] at H3
  refine H3.trans ?_
  have ht := abs_nonneg t
  have hT : 2 ≤ |t| + 2 := by linarith
  set T := |t| + 2
  have hl2 : Real.log 2 ≤ Real.log T := Real.log_le_log two_pos hT
  have hl := Real.log_two_gt_d9
  have hn : 0 < ‖riemannZeta₁ c‖ := by linarith
  have h1 : 5 * T ^ 2 / ‖riemannZeta₁ c‖ ≤ T ^ 7 := by
    rw [div_le_iff₀ hn]
    have h5 : (2 : ℝ) ^ 5 ≤ T ^ 5 := by gcongr
    have h6 : 5 ≤ T ^ 5 * ‖riemannZeta₁ c‖ := by nlinarith
    calc 5 * T ^ 2 ≤ (T ^ 5 * ‖riemannZeta₁ c‖) * T ^ 2 := by gcongr
      _ = _ := by ring
  have h2 := Real.log_le_log (by positivity) h1
  rw [Real.log_pow] at h2
  push_cast at h2
  have : 1 + Real.log (5 * T ^ 2 / ‖riemannZeta₁ c‖) ≤ 9 * Real.log T := by linarith
  nlinarith

end GlobalTheory.ZetaLocal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LogDerivRiemannZetaLocalZeroSumStatement
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.logDeriv_riemannZeta_local_zero_sum : ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ) (s : ℂ), ‖s - (3/2 + t * I)‖ ≤ 2/3 → s ≠ 1 → riemannZeta s ≠ 0 → {w : ℂ | ‖w - (3/2 + t * I)‖ ≤ 5/6 ∧ w ≠ 1 ∧ riemannZeta w = 0}.Finite ∧ ‖deriv riemannZeta s / riemannZeta s + 1 / (s - 1) - ∑ᶠ w ∈ {w : ℂ | ‖w - (3/2 + t * I)‖ ≤ 5/6 ∧ w ≠ 1 ∧ riemannZeta w = 0}, (analyticOrderNatAt riemannZeta w : ℂ) / (s - w)‖ ≤ C * Real.log (|t| + 2) := by
  first | exact @GlobalTheory.ZetaLocal.logDeriv_riemannZeta_local | exact GlobalTheory.ZetaLocal.logDeriv_riemannZeta_local | (intros; apply GlobalTheory.ZetaLocal.logDeriv_riemannZeta_local <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsBruhatFunctionClosedSubgroup
open MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
open scoped ENNReal

namespace GlobalTheory

open MeasureTheory Topology in
open scoped ENNReal Pointwise in
private theorem exists_normalized_weight_of_closedEmbedding
    {T T' : Type} [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T]
    [SecondCountableTopology T] [T2Space T] [MeasurableSpace T] [BorelSpace T]
    [Group T'] [TopologicalSpace T'] [IsTopologicalGroup T'] [MeasurableSpace T'] [BorelSpace T']
    (j : T' →* T) (hj : IsClosedEmbedding j) (ν : Measure T') [ν.IsHaarMeasure] :
    ∃ φ : T → ℝ≥0∞, Measurable φ ∧ (∀ g, ∫⁻ s, φ (g * j s) ∂ν = 1) ∧
      ∀ K : Set T, IsCompact K → ∃ (K' : Set T) (C : ℝ≥0∞), IsCompact K' ∧ C < ⊤ ∧
        ∀ k ∈ K, ∀ s : T', φ (k * j s) ≤ C ∧ (φ (k * j s) ≠ 0 → k * j s ∈ K') := by
  classical
  haveI : LocallyCompactSpace T' := hj.locallyCompactSpace
  haveI : SecondCountableTopology T' := hj.isEmbedding.secondCountableTopology
  haveI : T2Space T' := hj.isEmbedding.t2Space
  have hjm : Measurable j := hj.continuous.measurable
  let E := CompactExhaustion.choice T
  obtain ⟨A, hA⟩ : ∃ A : ℕ → Set T, ∀ n x, x ∈ A n ↔ ∃ s : T', x * j s ∈ E n :=
    ⟨fun n => {x | ∃ s : T', x * j s ∈ E n}, fun _ _ => Iff.rfl⟩
  have hA_mono : ∀ {m n}, m ≤ n → A m ⊆ A n := fun hmn x hx => by
    obtain ⟨s, hs⟩ := (hA _ x).1 hx
    exact (hA _ x).2 ⟨s, E.subset hmn hs⟩
  have hA_mul : ∀ n x (s : T'), x * j s ∈ A n ↔ x ∈ A n := by
    intro n x s
    rw [hA, hA]
    constructor
    · rintro ⟨s', hs'⟩
      exact ⟨s * s', by simpa [mul_assoc] using hs'⟩
    · rintro ⟨s', hs'⟩
      exact ⟨s⁻¹ * s', by simpa [mul_assoc] using hs'⟩
  have hE_A : ∀ n, E n ⊆ A n := fun n x hx => (hA n x).2 ⟨1, by simpa using hx⟩
  have hA_meas : ∀ n, MeasurableSet (A n) := by
    intro n
    have hAn : A n = E n * Set.range j := by
      ext x
      rw [hA, Set.mem_mul]
      constructor
      · rintro ⟨s, hs⟩
        exact ⟨_, hs, j s⁻¹, ⟨s⁻¹, rfl⟩, by simp [mul_assoc]⟩
      · rintro ⟨k, hk, _, ⟨s, rfl⟩, rfl⟩
        exact ⟨s⁻¹, by simpa [mul_assoc] using hk⟩
    rw [hAn]
    exact (hj.isClosed_range.mul_left_of_isCompact (E.isCompact n)).measurableSet
  have hex : ∀ x, ∃ n, x ∈ A n := fun x => ⟨E.find x, hE_A _ (E.mem_find x)⟩
  obtain ⟨N, hNm, hN⟩ : ∃ N : T → ℕ, Measurable N ∧ ∀ x n, N x ≤ n ↔ x ∈ A n := by
    refine ⟨fun x => Nat.find (hex x), measurable_find hex hA_meas, fun x n => ?_⟩
    rw [Nat.find_le_iff]
    exact ⟨fun ⟨m, hm, hx⟩ => hA_mono hm hx, fun hx => ⟨n, le_rfl, hx⟩⟩
  have hN_mem : ∀ x, x ∈ A (N x) := fun x => (hN x _).1 le_rfl
  have hN_mul : ∀ x (s : T'), N (x * j s) = N x := fun x s =>
    le_antisymm ((hN _ _).2 ((hA_mul _ _ _).2 (hN_mem x)))
      ((hN _ _).2 ((hA_mul _ _ _).1 (hN_mem _)))
  obtain ⟨S, hS⟩ : ∃ S : Set T, ∀ x, x ∈ S ↔ x ∈ E (N x + 1) :=
    ⟨{x | x ∈ E (N x + 1)}, fun _ => Iff.rfl⟩
  have hS_meas : MeasurableSet S := by
    have hSU : S = ⋃ n, N ⁻¹' {n} ∩ E (n + 1) := by
      ext x
      rw [hS]
      simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨fun hx => ⟨_, rfl, hx⟩, by rintro ⟨n, rfl, hx⟩; exact hx⟩
    rw [hSU]
    exact MeasurableSet.iUnion fun n =>
      (hNm (measurableSet_singleton n)).inter (E.isCompact _).isClosed.measurableSet
  obtain ⟨ψ, hψm, hψle, hψS, hψ1⟩ : ∃ ψ : T → ℝ≥0∞, Measurable ψ ∧ (∀ x, ψ x ≤ 1) ∧
      (∀ x, ψ x ≠ 0 → x ∈ S) ∧ (∀ x, x ∈ S → ψ x = 1) := by
    refine ⟨S.indicator fun _ => 1, measurable_const.indicator hS_meas, fun x => ?_,
      fun x hx => ?_, fun x hx => Set.indicator_of_mem hx _⟩
    · by_cases hx : x ∈ S <;> simp [hx]
    · by_contra hxS
      exact hx (by simp [hxS])
  obtain ⟨F, hFm, hF⟩ : ∃ F : T → ℝ≥0∞, Measurable F ∧ ∀ x, F x = ∫⁻ s, ψ (x * j s) ∂ν :=
    ⟨fun x => ∫⁻ s, ψ (x * j s) ∂ν,
      (hψm.comp (measurable_fst.mul (hjm.comp measurable_snd))).lintegral_prod_right',
      fun _ => rfl⟩
  have hF_mul : ∀ x (s : T'), F (x * j s) = F x := by
    intro x s
    rw [hF, hF]
    simpa [mul_assoc] using lintegral_mul_left_eq_self (μ := ν) (fun t => ψ (x * j t)) s
  have hF_pos : ∀ n, ∃ c : ℝ≥0∞, 0 < c ∧ ∀ x, N x = n → c ≤ F x := by
    intro n
    obtain ⟨V, hV, hKV⟩ :=
      compact_open_separated_mul_right (E.isCompact n) isOpen_interior (E.subset_interior_succ n)
    have hVo : IsOpen (j ⁻¹' interior V) := isOpen_interior.preimage hj.continuous
    have hV1 : (1 : T') ∈ j ⁻¹' interior V := by
      simpa using mem_interior_iff_mem_nhds.2 hV
    refine ⟨ν (j ⁻¹' interior V), hVo.measure_pos ν ⟨1, hV1⟩, fun x hx => ?_⟩
    obtain ⟨s₀, hs₀⟩ := (hA n x).1 (hx ▸ hN_mem x)
    calc ν (j ⁻¹' interior V) = ∫⁻ s, (j ⁻¹' interior V).indicator 1 s ∂ν :=
          (lintegral_indicator_one hVo.measurableSet).symm
      _ ≤ ∫⁻ s, ψ (x * j s₀ * j s) ∂ν := by
          refine lintegral_mono fun s => ?_
          by_cases hs : s ∈ j ⁻¹' interior V
          · rw [Set.indicator_of_mem hs, Pi.one_apply, hψ1]
            rw [hS, hN_mul, hN_mul, hx]
            exact interior_subset (hKV (Set.mul_mem_mul hs₀ (interior_subset hs)))
          · simp [hs]
      _ = F x := by rw [← hF, hF_mul]
  choose c hc_pos hc using hF_pos
  have hF_ne : ∀ x, F x ≠ 0 := fun x => ((hc_pos (N x)).trans_le (hc _ x rfl)).ne'
  have hF_fin : ∀ x, F x ≠ ⊤ := by
    intro x
    have hK : IsCompact ((fun s : T' => x * j s) ⁻¹' E (N x + 1)) :=
      ((Homeomorph.mulLeft x).isClosedEmbedding.comp hj).isCompact_preimage (E.isCompact _)
    refine (lt_of_le_of_lt ?_ (hK.measure_lt_top (μ := ν))).ne
    calc F x = ∫⁻ s, ψ (x * j s) ∂ν := hF x
      _ ≤ ∫⁻ s, ((fun s : T' => x * j s) ⁻¹' E (N x + 1)).indicator 1 s ∂ν := by
          refine lintegral_mono fun s => ?_
          by_cases hs : s ∈ (fun s : T' => x * j s) ⁻¹' E (N x + 1)
          · rw [Set.indicator_of_mem hs]
            exact hψle _
          · rw [Set.indicator_of_notMem hs]
            refine le_of_eq (by_contra fun hψs => ?_)
            have hmem := (hS _).1 (hψS _ hψs)
            rw [hN_mul] at hmem
            exact hs hmem
      _ = ν ((fun s : T' => x * j s) ⁻¹' E (N x + 1)) :=
          lintegral_indicator_one hK.isClosed.measurableSet
  refine ⟨fun x => ψ x * (F x)⁻¹, hψm.mul hFm.inv, fun g => ?_, fun K hK => ?_⟩
  · calc ∫⁻ s, ψ (g * j s) * (F (g * j s))⁻¹ ∂ν = ∫⁻ s, ψ (g * j s) * (F g)⁻¹ ∂ν := by
          simp_rw [hF_mul]
      _ = (∫⁻ s, ψ (g * j s) ∂ν) * (F g)⁻¹ :=
          lintegral_mul_const' _ _ (ENNReal.inv_ne_top.2 (hF_ne g))
      _ = 1 := by rw [← hF, ENNReal.mul_inv_cancel (hF_ne g) (hF_fin g)]
  · obtain ⟨M, hM⟩ := E.exists_superset_of_isCompact hK
    refine ⟨E (M + 1), ∑ n ∈ Finset.range (M + 1), (c n)⁻¹, E.isCompact _,
      ENNReal.sum_lt_top.2 fun n _ => ENNReal.inv_lt_top.2 (hc_pos n), fun k hk s => ⟨?_, ?_⟩⟩
    · have hNk : N k ≤ M := (hN k M).2 (hE_A M (hM hk))
      calc ψ (k * j s) * (F (k * j s))⁻¹ ≤ 1 * (c (N k))⁻¹ :=
            mul_le_mul' (hψle _) (ENNReal.inv_le_inv.2 (hc _ _ (hN_mul k s)))
        _ = (c (N k))⁻¹ := one_mul _
        _ ≤ ∑ n ∈ Finset.range (M + 1), (c n)⁻¹ :=
            Finset.single_le_sum (f := fun n => (c n)⁻¹) (fun _ _ => bot_le)
              (Finset.mem_range.2 (Nat.lt_succ_of_le hNk))
    · intro hne
      have hNk : N k ≤ M := (hN k M).2 (hE_A M (hM hk))
      have hmem := (hS _).1 (hψS _ (left_ne_zero_of_mul hne))
      rw [hN_mul] at hmem
      exact E.subset (Nat.succ_le_succ hNk) hmem

theorem _root_.GlobalTheory.exists_bruhat_function_closed_subgroup
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (H : Subgroup G)
    (hH : IsClosed (H : Set G)) (ν : Measure H) [ν.IsHaarMeasure] :
    ∃ φ : G → ℝ≥0∞, Measurable φ ∧ (∀ g : G, ∫⁻ h : H, φ (g * h) ∂ν = 1) ∧
      ∀ K : Set G, IsCompact K → ∃ (K' : Set G) (C : ℝ≥0∞), IsCompact K' ∧ C < ⊤ ∧
        ∀ k ∈ K, ∀ h : H, φ (k * h) ≤ C ∧ (φ (k * h) ≠ 0 → k * h ∈ K') := by
  obtain ⟨φ, hφm, hφ, hφK⟩ :=
    exists_normalized_weight_of_closedEmbedding H.subtype hH.isClosedEmbedding_subtypeVal ν
  exact ⟨φ, hφm, hφ, hφK⟩

end GlobalTheory
end
