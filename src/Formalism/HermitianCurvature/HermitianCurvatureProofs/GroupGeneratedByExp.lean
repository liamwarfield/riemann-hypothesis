module

public import Formalism.HermitianCurvature.FrameExists2
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LeftTypeAction
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedA
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuadraticFormTwoTwo.RadialDecompositionOfParts

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.GroupGeneratedByExp
open Matrix Finset Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

namespace GroupGeneratedByExp

section Banach

variable {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

theorem norm_pow_mul_le (x u : 𝔸) (n : ℕ) : ‖x ^ n * u‖ ≤ ‖x‖ ^ n * ‖u‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_assoc, pow_succ', mul_assoc]
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left ih (norm_nonneg _))

theorem norm_exp_mul_le (x u : 𝔸) : ‖NormedSpace.exp x * u‖ ≤ Real.exp ‖x‖ * ‖u‖ := by
  have h1 : HasSum (fun n : ℕ => (((n.factorial : ℝ)⁻¹) • x ^ n) * u) (NormedSpace.exp x * u) :=
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) x).mul_right u
  have h2 : HasSum (fun n : ℕ => (((n.factorial : ℝ)⁻¹) • ‖x‖ ^ n) * ‖u‖) (Real.exp ‖x‖ * ‖u‖) := by
    rw [Real.exp_eq_exp_ℝ]
    exact (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) ‖x‖).mul_right ‖u‖
  refine h1.norm_le_of_bounded h2 fun n => ?_
  rw [smul_mul_assoc, norm_smul, smul_eq_mul, mul_assoc, Real.norm_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left (norm_pow_mul_le x u n) (by positivity)

theorem norm_pow_mul_le' {a : 𝔸} {q : ℝ} (hq : 0 ≤ q) (ha : ∀ u, ‖a * u‖ ≤ q * ‖u‖) (m : ℕ) (u : 𝔸) :
    ‖a ^ m * u‖ ≤ q ^ m * ‖u‖ := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', mul_assoc, pow_succ', mul_assoc]
    exact (ha _).trans (mul_le_mul_of_nonneg_left ih hq)

theorem norm_pow_sub_pow_le {a b : 𝔸} {q : ℝ} (hq : 1 ≤ q) (ha : ∀ u, ‖a * u‖ ≤ q * ‖u‖)
    (hb : ∀ u, ‖b * u‖ ≤ q * ‖u‖) (m : ℕ) :
    ‖a ^ m - b ^ m‖ ≤ (m : ℝ) * q ^ m * (‖a - b‖ * ‖(1 : 𝔸)‖) := by
  have hq0 : 0 ≤ q := zero_le_one.trans hq
  induction m with
  | zero => simp
  | succ m ih =>
    have e : a ^ (m + 1) - b ^ (m + 1) = a * (a ^ m - b ^ m) + (a - b) * b ^ m := by
      rw [pow_succ', pow_succ']; noncomm_ring
    have h1 : ‖a * (a ^ m - b ^ m)‖ ≤ q * ((m : ℝ) * q ^ m * (‖a - b‖ * ‖(1 : 𝔸)‖)) :=
      (ha _).trans (mul_le_mul_of_nonneg_left ih hq0)
    have h2 : ‖b ^ m‖ ≤ q ^ (m + 1) * ‖(1 : 𝔸)‖ := by
      have := norm_pow_mul_le' hq0 hb m 1
      rw [mul_one] at this
      refine this.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
      exact pow_le_pow_right₀ hq (Nat.le_succ m)
    have h3 : ‖(a - b) * b ^ m‖ ≤ ‖a - b‖ * (q ^ (m + 1) * ‖(1 : 𝔸)‖) :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left h2 (norm_nonneg _))
    rw [e]
    refine (norm_add_le _ _).trans ((add_le_add h1 h3).trans (le_of_eq ?_))
    push_cast
    ring

theorem diff_hasDerivAt (X Y : 𝔸) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp (t • X) * NormedSpace.exp (t • Y) - NormedSpace.exp (t • (X + Y))) 0 0 := by
  have h1 := hasDerivAt_exp_smul_const (𝕂 := ℝ) X 0
  have h2 := hasDerivAt_exp_smul_const (𝕂 := ℝ) Y 0
  have h3 := hasDerivAt_exp_smul_const (𝕂 := ℝ) (X + Y) 0
  have h := (h1.mul h2).sub h3
  simp only [zero_smul, NormedSpace.exp_zero, one_mul, mul_one, sub_self] at h
  exact h

theorem trotter (X Y : 𝔸) :
    Tendsto (fun n : ℕ => (NormedSpace.exp (((n : ℝ)⁻¹) • X) * NormedSpace.exp (((n : ℝ)⁻¹) • Y)) ^ n) atTop
      (𝓝 (NormedSpace.exp (X + Y))) := by
  let _ : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  set s : ℝ := ‖X‖ + ‖Y‖ with hs
  have hs0 : 0 ≤ s := by positivity
  set F : ℝ → 𝔸 := fun t : ℝ =>
    NormedSpace.exp (t • X) * NormedSpace.exp (t • Y) - NormedSpace.exp (t • (X + Y)) with hF
  have hF0 : F 0 = 0 := by simp [hF, NormedSpace.exp_zero]
  have hsl := (diff_hasDerivAt X Y).tendsto_slope_zero
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ)⁻¹)) atTop (𝓝[≠] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨tendsto_inv_atTop_nhds_zero_nat, ?_⟩
    filter_upwards [eventually_gt_atTop 0] with n hn
    have : (0 : ℝ) < n := by exact_mod_cast hn
    exact (inv_pos.2 this).ne'
  have h1 : Tendsto (fun n : ℕ => (n : ℝ) • F ((n : ℝ)⁻¹)) atTop (𝓝 0) := by
    have := hsl.comp hinv
    refine this.congr fun n => ?_
    simp only [Function.comp, zero_add, inv_inv]
    rw [show NormedSpace.exp ((0 : ℝ) • X) * NormedSpace.exp ((0 : ℝ) • Y) - NormedSpace.exp ((0 : ℝ) • (X + Y)) = 0
      from hF0, sub_zero]
  have h2 : Tendsto (fun n : ℕ => Real.exp s * ‖(1 : 𝔸)‖ * ‖(n : ℝ) • F ((n : ℝ)⁻¹)‖) atTop (𝓝 0) := by
    have := (h1.norm).const_mul (Real.exp s * ‖(1 : 𝔸)‖)
    simpa using this
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_ h2
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hni : (0 : ℝ) ≤ (n : ℝ)⁻¹ := (inv_pos.2 hn0).le
  have hb : NormedSpace.exp (X + Y) = NormedSpace.exp (((n : ℝ)⁻¹) • (X + Y)) ^ n := by
    rw [← NormedSpace.exp_nsmul, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, mul_inv_cancel₀ hn0.ne', one_smul]
  have hq : (1 : ℝ) ≤ Real.exp ((n : ℝ)⁻¹ * s) := Real.one_le_exp (by positivity)
  have ha : ∀ u : 𝔸, ‖NormedSpace.exp (((n : ℝ)⁻¹) • X) * NormedSpace.exp (((n : ℝ)⁻¹) • Y) * u‖ ≤
      Real.exp ((n : ℝ)⁻¹ * s) * ‖u‖ := by
    intro u
    rw [mul_assoc]
    refine (norm_exp_mul_le _ _).trans ?_
    refine (mul_le_mul_of_nonneg_left (norm_exp_mul_le _ _) (Real.exp_pos _).le).trans (le_of_eq ?_)
    rw [← mul_assoc, ← Real.exp_add, norm_smul, norm_smul, Real.norm_of_nonneg hni, hs, mul_add]
  have hb' : ∀ u : 𝔸, ‖NormedSpace.exp (((n : ℝ)⁻¹) • (X + Y)) * u‖ ≤ Real.exp ((n : ℝ)⁻¹ * s) * ‖u‖ := by
    intro u
    refine (norm_exp_mul_le _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    rw [Real.exp_le_exp, norm_smul, Real.norm_of_nonneg hni]
    exact mul_le_mul_of_nonneg_left (norm_add_le _ _) hni
  rw [hb]
  refine (norm_pow_sub_pow_le hq ha hb' n).trans (le_of_eq ?_)
  rw [← Real.exp_nat_mul, show (n : ℝ) * ((n : ℝ)⁻¹ * s) = s by field_simp, norm_smul, Real.norm_of_nonneg hn0.le]
  ring

end Banach

theorem trotterMx (N : ℕ) (X Y : Matrix (Fin N) (Fin N) ℂ) :
    Tendsto (fun n : ℕ => (NormedSpace.exp ((((n : ℝ)⁻¹ : ℝ) : ℂ) • X) * NormedSpace.exp ((((n : ℝ)⁻¹ : ℝ) : ℂ) • Y)) ^ n) atTop
      (𝓝 (NormedSpace.exp (X + Y))) := by
  let _ := Matrix.linftyOpNormedRing (n := Fin N) (α := ℂ)
  let _ := Matrix.linftyOpNormedAlgebra (R := ℝ) (n := Fin N) (α := ℂ)
  have hc : CompleteSpace (Matrix (Fin N) (Fin N) ℂ) := FiniteDimensional.complete ℝ _
  have h := trotter X Y
  simp only [Complex.coe_smul]
  exact h

section Rep

variable {k r : ℕ} {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]

theorem group_eq_exp (φ : ℝ → (W →L[ℂ] W)) (A : W →L[ℂ] W) (h0 : φ 0 = 1)
    (hA : ∀ t, HasDerivAt φ ((φ t).comp A) t) (t : ℝ) : φ t = NormedSpace.exp (t • A) := by
  have hcW : CompleteSpace W := FiniteDimensional.complete ℂ W
  let _ : NormedAlgebra ℚ (W →L[ℂ] W) := NormedAlgebra.restrictScalars ℚ ℂ (W →L[ℂ] W)
  have hE : ∀ s : ℝ, HasDerivAt (fun u : ℝ => NormedSpace.exp (u • (-A)))
      ((-A) * NormedSpace.exp (s • (-A))) s := fun s => hasDerivAt_exp_smul_const' (𝕂 := ℝ) (-A) s
  have hψ : ∀ s : ℝ, HasDerivAt (fun u : ℝ => φ u * NormedSpace.exp (u • (-A))) 0 s := by
    intro s
    have h := (hA s).mul (hE s)
    have e : (φ s).comp A * NormedSpace.exp (s • (-A)) + φ s * ((-A) * NormedSpace.exp (s • (-A))) = 0 := by
      show φ s * A * _ + _ = 0
      noncomm_ring
    rwa [e] at h
  have hconst := is_const_of_deriv_eq_zero (𝕜 := ℝ) (fun s => (hψ s).differentiableAt) (fun s => (hψ s).deriv) t 0
  simp only [zero_smul, NormedSpace.exp_zero, h0, mul_one] at hconst
  have hinv : NormedSpace.exp (t • (-A)) * NormedSpace.exp (t • A) = 1 := by
    rw [← NormedSpace.exp_add_of_commute, smul_neg, neg_add_cancel, NormedSpace.exp_zero]
    exact (((Commute.refl A).neg_left).smul_left _).smul_right _
  calc φ t = φ t * (NormedSpace.exp (t • (-A)) * NormedSpace.exp (t • A)) := by rw [hinv, mul_one]
    _ = NormedSpace.exp (t • A) := by rw [← mul_assoc, hconst, one_mul]

end Rep

end GroupGeneratedByExp

theorem trotter_product_formula : Qr.Trotter := by
  intro 𝔸 _ _ _ X Y
  exact GroupGeneratedByExp.trotter X Y

theorem trotter_product_matrices : Qr.TrotterMx := by
  intro N X Y
  exact GroupGeneratedByExp.trotterMx N X Y

theorem representation_exp : Qr.PiExp := by
  intro W _ _ _ k r z π hπ X hX t
  have hcont : Continuous fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • X)) := by
    have h1 := Qx8.lcurve_cont X (1 : Mx k r)
    simp only [Matrix.mul_one] at h1
    exact hπ.2.comp_continuous h1 (QrD.exp_uw hX)
  have h0 : (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • X))) 0 = 1 := by
    simp [NormedSpace.exp_zero, hπ.1.1]
  obtain ⟨A, hA⟩ := one_parameter_differentiable W (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • X))) h0
    (fun s t => by
      show π (NormedSpace.exp (((s + t : ℝ) : ℂ) • X)) = _
      rw [B5.exp_add', hπ.1.2 _ (QrD.exp_uw hX s) _ (QrD.exp_uw hX t)]) hcont
  have hAd : QrD.dOp π X = A := by
    have h := (QrD.dOp_hasDeriv hπ.1 hπ.2 hX).unique (hA 0)
    have h0' : π (NormedSpace.exp (((0 : ℝ) : ℂ) • X)) = 1 := h0
    rw [h, h0']
    exact ContinuousLinearMap.id_comp A
  have h := GroupGeneratedByExp.group_eq_exp _ A h0 hA t
  rw [hAd]
  exact h

end Formalism.FourierDecayAlt.P
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.AdmissibleAtomicFormOneReduction
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

noncomputable section

set_option maxHeartbeats 3200000

namespace Formalism.FourierDecayAlt.P

namespace UnipotentHaarMeasurability

open Formalism.FourierDecayAlt.ThreeDimData

theorem smooth_admissible_form_one_side : AtFormAdmOneOfSteps := by
  intro hSch hBC hNI hBB hSh hKF hZ hZD hIn k r ε lam h H _ _ _ σ w0 Wp _ _ _ _ z c u π μW μN μG νq hS
  have hS' := hS
  obtain ⟨hlam, hσ, -, -, hw0, -, -, -, -, hW, hN, hG, hq⟩ := hS'
  obtain ⟨hBC1, -, -, -⟩ := hBC hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS
  obtain ⟨d, hd, hSd⟩ := hSch k r ε lam H σ μG hlam hσ hG
  have hw0n : w0 ≠ 0 := by
    obtain ⟨P, -, hn1, -⟩ := hw0
    intro h0; rw [h0, norm_zero] at hn1; exact zero_ne_one hn1
  have hdeg : ∀ x : H, x ≠ 0 → PI.BesselPeriodGGP.fdegH μG σ x = d := fun x hx => DDSmoothness.fdeg_eq hd hSd hx
  have hmu := DDSmoothness.muSof_facts hW hN
  have hae := DDSmoothness.ae_UH_of_quot hG.2.2.1 hmu.1 hmu.2 hq
  have hAs : ∀ v : H, IsAdm σ w0 v → v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ := by
    intro v hv
    rcases hv with hv | hv
    · exact DDSmoothness.DD_smooth hIn.2.2.1 hlam hσ hw0 v hv
    · exact hIn.2.2.1 k r ε lam H σ hlam hσ v hv
  by_cases hnz : ∃ x ∈ DDsp σ w0, ∃ y ∈ DDsp σ w0, be z c π σ μW μN x y ≠ 0
  · obtain ⟨l, hl, hx1, hid⟩ := hSh hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS hnz
    have hK := hKF hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS l hl hx1 hid
    have hI : ∀ v : H, IsAdm σ w0 v → ∀ x ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ,
        be z c π σ μW μN x v = (innerSL ℂ (l v)).smulRight (l x) := by
      intro v hv x hx
      rcases hv with hv | hv
      · exact hid x hx v hv
      · exact hK v hv x hx
    refine ⟨l, hl, fun x hx v hv => ⟨hBC1 x hx v hv, hI v hv x hx⟩, ?_⟩
    intro x hx hx0 v hv
    have hNv := (hNI hIn hSch k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS x hx v hv (l v)).1
    rw [hI v hv v (hAs v hv)] at hNv
    simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply] at hNv
    rw [hdeg w0 hw0n] at hNv
    rw [hdeg x hx0]
    refine DDSmoothness.l2_norm_scaling _ _ (l v) _ _ (by positivity) hNv (hae.mono fun g hg => ?_)
    rw [hI v hv _ (PI.UnitaryGroupMassFormula.CapelliEig.smooth_right_action k r ε lam H σ hσ x hx _ hg)]
    simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]
  · push_neg at hnz
    have h0 := hZ hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS hnz
    have h0D := hZD hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS hnz
    refine ⟨fun _ => 0, DDSmoothness.bessel_zero, fun x hx v hv => ⟨hBC1 x hx v hv, ?_⟩,
      fun x _ _ v _ => by simp⟩
    show be z c π σ μW μN x v = _
    have hz0 : be z c π σ μW μN x v = 0 := by
      rcases hv with hv | hv
      · exact h0D v hv x hx
      · exact h0 v hv x hx
    rw [hz0]
    ext ξ; simp

end UnipotentHaarMeasurability

theorem admissible_atomic_form_one_reduction : Formalism.FourierDecayAlt.ThreeDimData.AtFormAdmOneOfSteps := UnipotentHaarMeasurability.smooth_admissible_form_one_side

end Formalism.FourierDecayAlt.P
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameExtension
open Matrix Finset

noncomputable section

namespace Formalism.FourierDecayAlt.P.FrameExtension

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.QrD

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem frame_weaken {k r m : ℕ} {z e : Fin (2 * r + k + 1) → ℂ} {Bs : Fin m → Fin (2 * r + k + 1) → ℂ}
    (h : IsFrameOf k r [z, e] Bs) : IsFrameOf k r [z] Bs := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨h1, h2, fun a v hv => h3 a v (by rw [List.mem_singleton] at hv; subst hv; simp)⟩

private theorem hpk_apply_comm (k r : ℕ) (t u : Fin (2 * r + k + 1)) : Hpk k r u t = Hpk k r t u := by
  have := t.isLt
  have := u.isLt
  simp only [Hpk, Fin.ext_iff]
  split_ifs <;> first | rfl | omega

private theorem star_hpk_apply (k r : ℕ) (t u : Fin (2 * r + k + 1)) : star (Hpk k r t u) = Hpk k r t u := by
  simp only [Hpk]
  split_ifs <;> simp

private theorem herm_hpk_eq_star_herm_swap (k r : ℕ) (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) v w = star (herm (Hpk k r) w v) := by
  simp only [herm, dotProduct, mulVec, Pi.star_apply, star_sum, star_mul', star_star, star_hpk_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun u _ => ?_
  rw [hpk_apply_comm]
  ring

theorem frame_snoc {k r m : ℕ} {z e : Fin (2 * r + k + 1) → ℂ} {Bs : Fin m → Fin (2 * r + k + 1) → ℂ}
    (h : IsFrameOf k r [z, e] Bs) (he : inWb k r e) (hez : herm (Hpk k r) e z = 0) (hee : herm (Hpk k r) e e = 1) :
    IsFrameOf k r [z] (Fin.snoc (α := fun _ => Fin (2 * r + k + 1) → ℂ) Bs e) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun a => ?_, fun a b => ?_, fun a v hv => ?_⟩
  · induction a using Fin.lastCases with
    | last => simpa using he
    | cast i => simpa using h1 i
  · induction a using Fin.lastCases with
    | last =>
      induction b using Fin.lastCases with
      | last => simpa using hee
      | cast j =>
        simp only [Fin.snoc_last, Fin.snoc_castSucc]
        rw [if_neg (Fin.castSucc_lt_last j).ne', herm_hpk_eq_star_herm_swap, h3 j e (by simp), star_zero]
    | cast i =>
      induction b using Fin.lastCases with
      | last =>
        simp only [Fin.snoc_last, Fin.snoc_castSucc]
        rw [if_neg (Fin.castSucc_lt_last i).ne, h3 i e (by simp)]
      | cast j =>
        simp only [Fin.snoc_castSucc]
        rw [h2 i j]
        simp [Fin.castSucc_inj]
  · rw [List.mem_singleton] at hv
    subst hv
    induction a using Fin.lastCases with
    | last => simpa using hez
    | cast i => simpa using h3 i v (by simp)

theorem subA_EB {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] {k r m : ℕ} (π : Mx k r → (W →L[ℂ] W))
    (Bs : Fin m → Fin (2 * r + k + 1) → ℂ) (e : Fin (2 * r + k + 1) → ℂ) :
    subA (EB π (Fin.snoc (α := fun _ => Fin (2 * r + k + 1) → ℂ) Bs e)) = EB π Bs := by
  funext a b
  simp [subA, EB, unitB, Fin.snoc_castSucc]

theorem prod_Icc_fin (n : ℕ) (f : ℕ → ℂ) : ∏ i ∈ Finset.Icc 1 (n + 1), f i = ∏ j : Fin (n + 1), f ((j : ℕ) + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_Icc_succ_top (by omega), ih, Fin.prod_univ_castSucc (n := n + 1)]
    simp

end Formalism.FourierDecayAlt.P.FrameExtension

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.P.QrD

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem qr_branchingK_of : Qr.BranchingAlg → Qr.FrameGl → Qr.LieStab → Qr.StabLie → Qr.FrameChange →
    Qr.FrameExists2 → Qr.BranchingK := by
  intro hBA hFG hLS hSL hFC hFE Wp _ _ _ n r z e π u β L hz hT hty hL hu he hez hee
  obtain ⟨hnt, hrep, hcont, -, hirr, hcap⟩ := hty
  have hR : IsRepW (n + 1) r z π := ⟨hrep, hcont⟩
  obtain ⟨Bs₀, hB₀⟩ := hFE n r z e hz hT he hez hee
  have hB₁ := FrameExtension.frame_snoc hB₀ he hez hee
  set Bs₁ : Fin (n + 1) → Fin (2 * r + (n + 1) + 1) → ℂ :=
    Fin.snoc (α := fun _ => Fin (2 * r + (n + 1) + 1) → ℂ) Bs₀ e with hBs₁
  have hsub : subA (EB π Bs₁) = EB π Bs₀ := FrameExtension.subA_EB π Bs₀ e
  obtain ⟨hgl, hq⟩ := hFG Wp (n + 1) r (n + 1) z π Bs₁ hR hB₁
  have hH : Hyp (EB π Bs₁) β L := by
    refine ⟨hgl, ⟨hnt, fun S hS => hirr S (hLS Wp (n + 1) r z π Bs₁ hz hT hR hB₁ S hS)⟩, hL, ?_⟩
    intro w v
    rw [← hq w v, hcap Bs₁ hB₁ w v, FrameExtension.prod_Icc_fin]
    congr 1
    unfold cpol shf
    refine Finset.prod_congr rfl (fun j _ => ?_)
    rw [← hu j]
    ring
  obtain ⟨hint, hS⟩ := hBA Wp n (EB π Bs₁) β L hH
  rw [hsub] at hint hS
  refine ⟨fun M => CapSp (EB π Bs₀) (shf β M.1), hint, fun M => ⟨(hS M).1, fun S' hle hst => ?_⟩, ?_⟩
  · exact (hS M).2 S' hle (hSL Wp (n + 1) r n z e π Bs₀ hR hB₀ S' hst)
  · intro Bs hBs M w v hv
    rw [(hFG Wp (n + 1) r n z π Bs hR (FrameExtension.frame_weaken hBs)).2 w v,
      hFC Wp n r z e π Bs Bs₀ hz hT he hez hee hR hBs hB₀ w]
    exact Qr.mem_CapSp.1 hv w

end Formalism.FourierDecayAlt.P
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.ProductIntervalFrames
open Matrix Finset

noncomputable section

namespace Formalism.FourierDecayAlt.P.ProductIntervalFrames

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr

theorem isInternal_comp {ι κ W : Type*} [DecidableEq ι] [DecidableEq κ] [AddCommGroup W] [Module ℂ W]
    (Φ : ι → κ) (hΦ : Function.Bijective Φ) (S : κ → Submodule ℂ W) (h : DirectSum.IsInternal S) :
    DirectSum.IsInternal (fun i => S (Φ i)) := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top] at h ⊢
  exact ⟨h.1.comp hΦ.1, by rw [hΦ.2.iSup_comp S]; exact h.2⟩

theorem prod_Icc_one (n : ℕ) (f : ℕ → ℂ) : ∏ i ∈ Icc 1 n, f i = ∏ j : Fin n, f ((j : ℕ) + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_Icc_succ_top (by omega), ih, Fin.prod_univ_castSucc (n := n)]
    simp

abbrev par (n r : ℕ) (T T' : ℝ) (u : ℕ → ℝ) : M.Par := ⟨n + 1, r, T, T', u, u⟩

theorem rho_eq (n r : ℕ) (T T' : ℝ) (u : ℕ → ℝ) (ρ : M.Ty (par n r T T' u)) (j : Fin n) :
    M.rho (par n r T T' u) ρ ((j : ℕ) + 1) = u ((j : ℕ) + 2) + 1 / 2 + (((ρ j : Fin _) : ℕ) : ℝ) := by
  have hj := j.isLt
  simp only [M.rho, M.Par.lo, par, max_self]
  rw [dite_eq_left ⟨by omega, by omega⟩]
  rfl

theorem wid_eq (n r : ℕ) (T T' : ℝ) (u : ℕ → ℝ) (L : Fin (n + 1) → ℤ)
    (hL : ∀ j : Fin (n + 1), u ((j : ℕ) + 1) - u 1 = (L j : ℝ))
    (hg : ∀ j : Fin n, L j.succ + 1 ≤ L j.castSucc) (j : Fin n) :
    (((par n r T T' u).wid ((j : ℕ) + 1) : ℕ) : ℤ) = L j.castSucc - L j.succ - 1 := by
  have h1 := hL j.castSucc
  have h2 := hL j.succ
  simp only [Fin.coe_castSucc, Fin.val_succ] at h1 h2
  have hd : (par n r T T' u).hi ((j : ℕ) + 1) - (par n r T T' u).lo ((j : ℕ) + 1) =
      ((L j.castSucc - L j.succ - 1 : ℤ) : ℝ) := by
    simp only [M.Par.hi, M.Par.lo, par, min_self, max_self]
    push_cast
    linarith
  have hnn : 0 ≤ L j.castSucc - L j.succ - 1 := by linarith [hg j]
  simp only [M.Par.wid]
  rw [hd, ← Int.floor_toNat, Int.floor_intCast, Int.toNat_of_nonneg hnn]

theorem main (hK : BranchingK) (Wp : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (n r : ℕ) (T T' : ℝ) (u : ℕ → ℝ) (hOK : (par n r T T' u).OK)
    (z e : Fin (2 * r + (n + 1) + 1) → ℂ) (π : Mx (n + 1) r → (Wp →L[ℂ] Wp)) (hz : inWb (n + 1) r z)
    (hT : 0 < Tz (n + 1) r z) (hπ : IsType (n + 1) r z π u) (he : inWb (n + 1) r e)
    (hez : herm (Hpk (n + 1) r) e z = 0) (hee : herm (Hpk (n + 1) r) e e = 1) :
    ∃ S : M.Ty (par n r T T' u) → Submodule ℂ Wp, DirectSum.IsInternal S ∧
      (∀ ρ, S ρ ≠ ⊥ ∧ ∀ S' : Submodule ℂ Wp, S' ≤ S ρ →
        (∀ h ∈ UWset (n + 1) r z, h *ᵥ e = e → ∀ v ∈ S', π h v ∈ S') → S' = ⊥ ∨ S' = S ρ) ∧
      ∀ Bs : Fin n → Fin (2 * r + (n + 1) + 1) → ℂ, IsFrameOf (n + 1) r [z, e] Bs →
        ∀ (ρ : M.Ty (par n r T T' u)) (w : ℂ), ∀ v ∈ S ρ,
        capRep (n + 1) r π Bs w v = M.xC (par n r T T' u) ρ (w - (((n + 1 : ℕ) : ℂ) - 2) / 2) • v := by
  have hint : ∀ j : Fin (n + 1), ∃ N : ℤ, u ((j : ℕ) + 1) - u 1 = (N : ℝ) := fun j =>
    hOK.int_u ((j : ℕ) + 1) (by
      have := j.2
      rw [mem_Icc]
      constructor
      · omega
      · show (j : ℕ) + 1 ≤ n + 1
        omega)
  choose L hL using hint
  have hgap : ∀ j : Fin n, u ((j : ℕ) + 2) + 1 ≤ u ((j : ℕ) + 1) := fun j => by
    have h := hOK.gap ((j : ℕ) + 1) (by
      have := j.2
      rw [mem_Icc]
      constructor
      · omega
      · show (j : ℕ) + 1 ≤ n + 1 - 1
        omega)
    simp only [M.Par.lo, M.Par.hi, max_self, min_self] at h
    linarith
  have hg : ∀ j : Fin n, L j.succ + 1 ≤ L j.castSucc := fun j => by
    have h1 := hL j.castSucc
    have h2 := hL j.succ
    simp only [Fin.val_castSucc, Fin.val_succ] at h1 h2
    have h3 := hgap j
    have : (L j.succ : ℝ) + 1 ≤ (L j.castSucc : ℝ) := by linarith
    exact_mod_cast this
  have hanti : StrictAnti L := Fin.strictAnti_iff_succ_lt.2 fun j => by have := hg j; omega
  have hw := wid_eq n r T T' u L hL hg
  set β : ℂ := (u 1 : ℂ) - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2 with hβ
  have hrel : ∀ j : Fin (n + 1), (u ((j : ℕ) + 1) : ℂ) - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2 = β + (L j : ℂ) := fun j => by
    have h : (u ((j : ℕ) + 1) : ℂ) - (u 1 : ℂ) = (L j : ℂ) := by exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) (hL j)
    rw [hβ, ← h]
    ring
  obtain ⟨S₀, hint₀, hirr, heig⟩ := hK Wp n r z e π u β L hz hT hπ hanti hrel he hez hee
  let Φ : M.Ty (par n r T T' u) → {M : Fin n → ℤ // Box L M} := fun ρ =>
    ⟨fun j => L j.succ + 1 + (((ρ j : Fin _) : ℕ) : ℤ), fun j => by
      have h1 := (ρ j).2
      have h2 := hw j
      constructor
      · show L j.succ < L j.succ + 1 + (((ρ j : Fin _) : ℕ) : ℤ)
        omega
      · show L j.succ + 1 + (((ρ j : Fin _) : ℕ) : ℤ) ≤ L j.castSucc
        omega⟩
  have hΦ : Function.Bijective Φ := by
    constructor
    · intro ρ ρ' h
      funext j
      have h1 := congrFun (congrArg Subtype.val h) j
      simp only [Φ] at h1
      apply Fin.ext
      omega
    · intro M
      refine ⟨fun j => ⟨(M.1 j - L j.succ - 1).toNat, ?_⟩, ?_⟩
      · have h1 := M.2 j
        have h2 := hw j
        omega
      · apply Subtype.ext
        funext j
        have h1 := M.2 j
        simp only [Φ]
        omega
  refine ⟨fun ρ => S₀ (Φ ρ), isInternal_comp Φ hΦ S₀ hint₀, fun ρ => hirr (Φ ρ), ?_⟩
  intro Bs hBs ρ w v hv
  rw [heig Bs hBs (Φ ρ) w v hv]
  congr 1
  unfold M.xC cpol
  rw [show (par n r T T' u).k - 1 = n from rfl, prod_Icc_one]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [rho_eq]
  have h : (u ((j : ℕ) + 2) : ℂ) - (u 1 : ℂ) = (L j.succ : ℂ) := by
    have := hL j.succ
    simp only [Fin.val_succ] at this
    exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) this
  simp only [shf, Φ, hβ]
  push_cast
  rw [← h]
  ring

end Formalism.FourierDecayAlt.P.ProductIntervalFrames

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr

theorem qr_branching_of : Qr.BranchingK → Formalism.FourierDecayAlt.Q.Branching := by
  intro hK Wp _ _ _ P hOK hu'
  obtain ⟨k, r, T, T', u, u'⟩ := P
  dsimp only at hu'
  subst hu'
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by have := hOK.k_pos; dsimp only at this; omega⟩
  intro z e π hz hT hπ he hez hee
  exact ProductIntervalFrames.main hK Wp n r T T' _ hOK z e π hz hT hπ he hez hee

end Formalism.FourierDecayAlt.P
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.BlockOfCauchySchwarz
open Finset
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P.PBA

open Formalism.FourierDecayAlt

section block

variable {α β : Type} (Y₁ : Finset α) (Y₂ : Finset β)

noncomputable def qf {γ : Type} (Y : Finset γ) (k : γ → γ → ℂ) (c : γ → ℂ) : ℂ :=
  ∑ x ∈ Y, ∑ y ∈ Y, conj (c x) * k x y * c y

def blockK (a : α → α → ℂ) (w : α → β → ℂ) (b : β → β → ℂ) : α ⊕ β → α ⊕ β → ℂ :=
  fun x y => match x, y with
    | .inl p, .inl q => a p q
    | .inl p, .inr q => w p q
    | .inr q, .inl p => conj (w p q)
    | .inr p, .inr q => b p q

theorem blockPSD_iff (a : α → α → ℂ) (w : α → β → ℂ) (b : β → β → ℂ) :
    KB.BlockPSD Y₁ Y₂ a w b ↔ TB.PSDOn (Y₁.disjSum Y₂) (blockK a w b) := by
  unfold KB.BlockPSD blockK
  exact Iff.rfl

theorem qf_block (a : α → α → ℂ) (w : α → β → ℂ) (b : β → β → ℂ) (c : α ⊕ β → ℂ) :
    (qf (Y₁.disjSum Y₂) (blockK a w b) c).re =
      (qf Y₁ a (fun p => c (.inl p))).re + (qf Y₂ b (fun q => c (.inr q))).re +
        2 * (∑ p ∈ Y₁, ∑ q ∈ Y₂, conj (c (.inl p)) * w p q * c (.inr q)).re := by
  have hconj : (∑ x ∈ Y₂, ∑ y ∈ Y₁, conj (c (.inr x)) * conj (w y x) * c (.inl y)) =
      conj (∑ p ∈ Y₁, ∑ q ∈ Y₂, conj (c (.inl p)) * w p q * c (.inr q)) := by
    rw [Finset.sum_comm]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, Complex.conj_conj]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    ring
  simp only [qf, Finset.sum_disjSum, blockK, Finset.sum_add_distrib]
  rw [hconj]
  simp only [Complex.add_re, Complex.conj_re]
  ring

theorem psd_iff_qf {γ : Type} (Y : Finset γ) (k : γ → γ → ℂ) :
    TB.PSDOn Y k ↔ (∀ x ∈ Y, ∀ y ∈ Y, k y x = conj (k x y)) ∧ ∀ c, 0 ≤ (qf Y k c).re := by
  classical
  have hqf : ∀ c : γ → ℂ, qf Y k c = ∑ i : Y, ∑ j : Y, conj (c i) * k i j * c j := by
    intro c
    unfold qf
    rw [← Finset.sum_coe_sort Y]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_coe_sort Y]
  have hsum : ∀ x : Y →₀ ℂ,
      (x.sum fun i xi => x.sum fun j xj => star xi * Matrix.of (fun x y : Y => k x y) i j * xj) =
        ∑ i : Y, ∑ j : Y, conj (x i) * k i j * x j := by
    intro x
    rw [Finsupp.sum_fintype _ _ (fun i => by simp)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finsupp.sum_fintype _ _ (fun j => by simp)]
    rfl
  unfold TB.PSDOn Matrix.PosSemidef
  constructor
  · rintro ⟨hH, hpos⟩
    refine ⟨fun x hx y hy => ?_, fun c => ?_⟩
    · have h1 := hH.apply ⟨y, hy⟩ ⟨x, hx⟩
      exact h1.symm
    · have h2 := hpos (Finsupp.equivFunOnFinite.symm fun i : Y => c i)
      rw [hsum] at h2
      rw [hqf]
      simpa using (Complex.le_def.mp h2).1
  · rintro ⟨hh, hq⟩
    refine ⟨Matrix.IsHermitian.ext fun i j => ?_, fun x => ?_⟩
    · simp only [Matrix.of_apply]
      rw [hh j j.2 i i.2]
      rfl
    · rw [hsum]
      have hre := hq (fun g => if h : g ∈ Y then x ⟨g, h⟩ else 0)
      rw [hqf] at hre
      have hc : ∀ i : Y, (if h : (i : γ) ∈ Y then x ⟨i, h⟩ else 0) = x i := fun i => by simp
      simp only [hc] at hre
      have him : (∑ i : Y, ∑ j : Y, conj (x i) * k i j * x j).im = 0 := by
        rw [← Complex.conj_eq_iff_im]
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_sum, map_mul, Complex.conj_conj]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [hh i i.2 j j.2, Complex.conj_conj]
        ring
      exact Complex.le_def.mpr ⟨by simpa using hre, by rw [Complex.zero_im, him]⟩

theorem block_quad {a : α → α → ℂ} {w : α → β → ℂ} {b : β → β → ℂ} (h : KB.BlockPSD Y₁ Y₂ a w b)
    (c : α → ℂ) (d : β → ℂ) :
    0 ≤ (qf Y₁ a c).re + (qf Y₂ b d).re + 2 * (∑ p ∈ Y₁, ∑ q ∈ Y₂, conj (c p) * w p q * d q).re := by
  have h1 := ((psd_iff_qf _ _).1 ((blockPSD_iff Y₁ Y₂ a w b).1 h)).2 (Sum.elim c d)
  rw [qf_block] at h1
  simpa using h1

end block

theorem cross_le {A B x : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (h : x ^ 2 ≤ A * B) (hx : 0 ≤ x) : 2 * x ≤ A + B := by
  have hAB : 0 ≤ A + B := by linarith
  by_contra hc
  push_neg at hc
  nlinarith [sq_nonneg (A - B), mul_nonneg hAB hx]

theorem block_of_cauchy_schwarz : KB.BlockOfCS := by
  intro α β Y₁ Y₂ a w b ha hb hcs
  have ha' := (psd_iff_qf Y₁ a).1 ha
  have hb' := (psd_iff_qf Y₂ b).1 hb
  rw [blockPSD_iff, psd_iff_qf]
  refine ⟨fun x hx y hy => ?_, fun c => ?_⟩
  · rcases x with p | q <;> rcases y with p' | q'
    · simpa [blockK] using ha'.1 p (by simpa using hx) p' (by simpa using hy)
    · simp [blockK]
    · simp [blockK]
    · simpa [blockK] using hb'.1 q (by simpa using hx) q' (by simpa using hy)
  · rw [qf_block]
    set X := ∑ p ∈ Y₁, ∑ q ∈ Y₂, conj (c (.inl p)) * w p q * c (.inr q) with hX
    have hA := ha'.2 (fun p => c (.inl p))
    have hB := hb'.2 (fun q => c (.inr q))
    have h1 := hcs (fun p => conj (c (.inl p))) (fun q => conj (c (.inr q)))
    have eX : (∑ p ∈ Y₁, ∑ q ∈ Y₂, conj (c (.inl p)) * conj (conj (c (.inr q))) * w p q) = X := by
      rw [hX]
      refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
      rw [Complex.conj_conj]
      ring
    have eA : (∑ p ∈ Y₁, ∑ p' ∈ Y₁, conj (c (.inl p)) * conj (conj (c (.inl p'))) * a p p') =
        qf Y₁ a (fun p => c (.inl p)) := by
      simp only [qf, Complex.conj_conj]
      refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
      ring
    have eB : (∑ q ∈ Y₂, ∑ q' ∈ Y₂, conj (c (.inr q)) * conj (conj (c (.inr q'))) * b q q') =
        qf Y₂ b (fun q => c (.inr q)) := by
      simp only [qf, Complex.conj_conj]
      refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
      ring
    rw [eX, eA, eB] at h1
    have hx := cross_le hA hB h1 (norm_nonneg X)
    have hre : -‖X‖ ≤ X.re := by
      have h2 := Complex.normSq_eq_norm_sq X
      rw [Complex.normSq_apply] at h2
      nlinarith [sq_nonneg X.im, norm_nonneg X]
    linarith

theorem blockPSD_mul {α β : Type} {Y₁ : Finset α} {Y₂ : Finset β} {a a' : α → α → ℂ} {w w' : α → β → ℂ}
    {b b' : β → β → ℂ} (h : KB.BlockPSD Y₁ Y₂ a w b) (h' : KB.BlockPSD Y₁ Y₂ a' w' b') :
    KB.BlockPSD Y₁ Y₂ (fun p q => a p q * a' p q) (fun p q => w p q * w' p q) (fun p q => b p q * b' p q) := by
  rw [blockPSD_iff] at *
  refine Jx7.psd_congr ?_ (Jx7.psd_mul h h')
  intro x _ y _
  rcases x with p | q <;> rcases y with p' | q' <;> simp [blockK, map_mul]

theorem blockPSD_ones {α β : Type} (Y₁ : Finset α) (Y₂ : Finset β) :
    KB.BlockPSD Y₁ Y₂ (fun _ _ => 1) (fun _ _ => 1) (fun _ _ => 1) := by
  rw [blockPSD_iff, psd_iff_qf]
  refine ⟨fun x _ y _ => ?_, fun c => ?_⟩
  · cases x <;> cases y <;> simp [blockK]
  · have hq : qf (Y₁.disjSum Y₂) (blockK (fun _ _ => (1 : ℂ)) (fun _ _ => 1) (fun _ _ => 1)) c =
        conj (∑ x ∈ Y₁.disjSum Y₂, c x) * ∑ x ∈ Y₁.disjSum Y₂, c x := by
      unfold qf
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
      cases x <;> cases y <;> simp [blockK]
    rw [hq, ← Complex.normSq_eq_conj_mul_self]
    simp [Complex.normSq_nonneg]

theorem blockPSD_prod {α β ι : Type} {Y₁ : Finset α} {Y₂ : Finset β} (s : Finset ι) (a : ι → α → α → ℂ)
    (w : ι → α → β → ℂ) (b : ι → β → β → ℂ) (h : ∀ v ∈ s, KB.BlockPSD Y₁ Y₂ (a v) (w v) (b v)) :
    KB.BlockPSD Y₁ Y₂ (fun p q => ∏ v ∈ s, a v p q) (fun p q => ∏ v ∈ s, w v p q)
      (fun p q => ∏ v ∈ s, b v p q) := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    simpa using blockPSD_ones Y₁ Y₂
  · intro v t hv ih h
    simp only [Finset.prod_insert hv]
    exact blockPSD_mul (h v (Finset.mem_insert_self v t)) (ih fun u hu => h u (Finset.mem_insert_of_mem hu))

theorem block_cross_le {α β : Type} {Y₁ : Finset α} {Y₂ : Finset β} {a : α → α → ℂ} {w : α → β → ℂ}
    {b : β → β → ℂ} (h : KB.BlockPSD Y₁ Y₂ a w b) :
    ‖∑ p ∈ Y₁, ∑ q ∈ Y₂, w p q‖ ≤ ((∑ p ∈ Y₁, ∑ p' ∈ Y₁, a p p').re + (∑ q ∈ Y₂, ∑ q' ∈ Y₂, b q q').re) / 2 := by
  have key : ∀ u v : ℂ, 0 ≤ Complex.normSq u * (∑ p ∈ Y₁, ∑ p' ∈ Y₁, a p p').re +
      Complex.normSq v * (∑ q ∈ Y₂, ∑ q' ∈ Y₂, b q q').re +
      2 * (conj u * v * ∑ p ∈ Y₁, ∑ q ∈ Y₂, w p q).re := by
    intro u v
    have h1 := block_quad Y₁ Y₂ h (fun _ => u) (fun _ => v)
    have e1 : qf Y₁ a (fun _ => u) = conj u * u * ∑ p ∈ Y₁, ∑ p' ∈ Y₁, a p p' := by
      simp only [qf]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      ring
    have e2 : qf Y₂ b (fun _ => v) = conj v * v * ∑ q ∈ Y₂, ∑ q' ∈ Y₂, b q q' := by
      simp only [qf]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      ring
    have e3 : (∑ p ∈ Y₁, ∑ q ∈ Y₂, conj u * w p q * v) = conj u * v * ∑ p ∈ Y₁, ∑ q ∈ Y₂, w p q := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      ring
    rw [e1, e2, e3, ← Complex.normSq_eq_conj_mul_self, ← Complex.normSq_eq_conj_mul_self,
      Complex.re_ofReal_mul, Complex.re_ofReal_mul] at h1
    exact h1
  set S := ∑ p ∈ Y₁, ∑ q ∈ Y₂, w p q with hS
  by_cases h0 : S = 0
  · have k1 := key 1 (-1)
    rw [h0] at k1
    simp at k1
    rw [h0, norm_zero]
    simp only [Complex.re_sum]
    linarith
  · have hn : 0 < ‖S‖ := norm_pos_iff.mpr h0
    have k2 := key S (-(‖S‖ : ℂ))
    have hns : Complex.normSq S = ‖S‖ ^ 2 := Complex.normSq_eq_norm_sq S
    have hnr : Complex.normSq (-(‖S‖ : ℂ)) = ‖S‖ ^ 2 := by
      rw [Complex.normSq_neg, Complex.normSq_ofReal]
      ring
    have hcr : (conj S * -(‖S‖ : ℂ) * S).re = -(‖S‖ ^ 3) := by
      have e : conj S * -(‖S‖ : ℂ) * S = -((‖S‖ : ℂ) * (Complex.normSq S : ℂ)) := by
        rw [Complex.normSq_eq_conj_mul_self]
        ring
      rw [e, hns, Complex.neg_re, Complex.re_ofReal_mul, Complex.ofReal_re]
      ring
    rw [hns, hnr, hcr] at k2
    nlinarith [mul_pos hn hn, k2]

end Formalism.FourierDecayAlt.P.PBA
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnCVInCC
open Formalism.FourierDecayAlt
open Formalism.REAL Formalism.QuantumDeterminants

namespace Formalism.FourierDecayAlt.P.CutMP.En

theorem inCC_wordSum {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {A : ℝ} {m n : ℕ}
    {F : B.Mat k r → E} (hF : B.InCC A (m + n) F) :
    ∀ L : List (ℂ × List (B.Mat k r)), (∀ cw ∈ L, (∀ X ∈ cw.2, B.unitLie k r X) ∧ cw.2.length ≤ n) →
      B.InCC A m (fun g => (L.map fun cw => cw.1 • B.Rw cw.2 F g).sum) := by
  intro L
  induction L with
  | nil =>
    intro _
    exact ⟨0, by simpa using (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_zero (k := k) (r := r) (E := E) (A := A) (m := m))⟩
  | cons cw L ih =>
    intro hL
    have h1 : B.InCC A m (fun g => cw.1 • B.Rw cw.2 F g) := by
      have hw := hL cw (by simp)
      have h0 : B.InCC A (m + cw.2.length) F :=
        Formalism.FourierDecayAlt.P.BetaSesquilinearity.sInCC_mono le_rfl (by omega) hF
      obtain ⟨c, hc⟩ := Formalism.FourierDecayAlt.P.BetaSesquilinearity.InCC_Rw (fun X hX => (hw.1 X hX).1) h0
      exact ⟨_, Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_smul cw.1 hc⟩
    have h2 := ih (fun cw' hcw' => hL cw' (List.mem_cons_of_mem cw hcw'))
    obtain ⟨c₁, hc₁⟩ := h1
    obtain ⟨c₂, hc₂⟩ := h2
    refine ⟨c₁ + c₂, ?_⟩
    simpa [List.map_cons, List.sum_cons] using Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_add hc₁ hc₂

theorem coefficient_vector_in_L2_class : CVInCC := by
  intro k r E _ _ A m F Y s hF
  obtain ⟨L, hLw, hCV⟩ := Formalism.FourierDecayAlt.P.capelli_word_sum k r Y
  have hck : B.CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) (B.GV k r) F := by
    obtain ⟨c, hc⟩ := hF
    exact Formalism.FourierDecayAlt.P.B5.ckOn_mono (by exact_mod_cast Nat.le_add_left _ _) hc.1
  obtain ⟨c, hc⟩ := inCC_wordSum hF L hLw
  refine ⟨_, Formalism.FourierDecayAlt.P.Qx8.CCle_congr (f := fun g => s • (L.map fun cw => cw.1 • B.Rw cw.2 F g).sum) ?_
    (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_smul s hc)⟩
  intro g hg
  rw [Pi.smul_apply, hCV E (B.GV k r) F hck g hg hg]

end Formalism.FourierDecayAlt.P.CutMP.En
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.QRadialDecompositionOfPieces
section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.RadialDecompositionOfParts
theorem radial_decomposition_of_parts : Formalism.FourierDecayAlt.Q.RadialDecompositionOfParts := Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.radial_decomposition_of_parts'
end

theorem Formalism.FourierDecayAlt.P.q_radial_decomposition_of_pieces : Formalism.FourierDecayAlt.Q.RadialDecompositionOfParts :=
  radial_decomposition_of_parts
end
