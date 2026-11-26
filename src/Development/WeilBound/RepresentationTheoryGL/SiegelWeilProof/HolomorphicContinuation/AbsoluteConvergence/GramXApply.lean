module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.NormDetFirstBlockCompact

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsRestExtra
namespace SupNormSqLeSumNormSq

private lemma entry_le {m n : ℕ} (x : Fin m → Fin n → ℂ) (a : Fin m) (j : Fin n) :
    ‖x a j‖ ≤ Real.sqrt (∑ a : Fin m, ∑ j : Fin n, ‖x a j‖ ^ (2 : ℕ)) := by
  apply Real.le_sqrt_of_sq_le
  calc ‖x a j‖ ^ (2 : ℕ) ≤ ∑ j : Fin n, ‖x a j‖ ^ (2 : ℕ) :=
        Finset.single_le_sum (f := fun j => ‖x a j‖ ^ (2 : ℕ)) (fun _ _ => by positivity)
          (Finset.mem_univ j)
    _ ≤ ∑ a : Fin m, ∑ j : Fin n, ‖x a j‖ ^ (2 : ℕ) :=
        Finset.single_le_sum (f := fun a => ∑ j : Fin n, ‖x a j‖ ^ (2 : ℕ))
          (fun _ _ => by positivity) (Finset.mem_univ a)

end SupNormSqLeSumNormSq

theorem UpperTheory.Reformulated.B.Yhb3.main :
    ∀ {m n : ℕ} (x : Fin m → Fin n → ℂ), ‖x‖ ^ (2 : ℕ) ≤ ∑ a : Fin m, ∑ j : Fin n, ‖x a j‖ ^ (2 : ℕ) := by
  intro m n x
  have hS : 0 ≤ ∑ a : Fin m, ∑ j : Fin n, ‖x a j‖ ^ (2 : ℕ) := by positivity
  have h : ‖x‖ ≤ Real.sqrt (∑ a : Fin m, ∑ j : Fin n, ‖x a j‖ ^ (2 : ℕ)) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun a => ?_
    exact (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun j => SupNormSqLeSumNormSq.entry_le x a j
  calc ‖x‖ ^ (2 : ℕ) ≤ (Real.sqrt (∑ a : Fin m, ∑ j : Fin n, ‖x a j‖ ^ (2 : ℕ))) ^ (2 : ℕ) :=
        pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = _ := Real.sq_sqrt hS
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.HasDerivAtEvalCurve
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.ContinuousEvX
noncomputable section

open MeasureTheory Matrix Set Filter Topology MvPolynomial

namespace PositivityTheory.Rg.Sw.AbsSt.DF

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

def ept (x : Fin m → Fin n → ℂ) : Fin m × Fin n × Bool → ℂ :=
  fun k => if k.2.2 then star (x k.1 k.2.1) else x k.1 k.2.1

theorem evX_eq (P : PX m n) (x : Fin m → Fin n → ℂ) : evX P x = MvPolynomial.eval (ept x) P := rfl

theorem norm_ept_le (x : Fin m → Fin n → ℂ) (k : Fin m × Fin n × Bool) : ‖ept x k‖ ≤ ‖x‖ := by
  have h : ‖x k.1 k.2.1‖ ≤ ‖x‖ := (norm_le_pi_norm (x k.1) k.2.1).trans (norm_le_pi_norm x k.1)
  unfold ept
  split_ifs
  · simpa using h
  · exact h

theorem continuous_ept : Continuous (ept : (Fin m → Fin n → ℂ) → _) := by
  refine continuous_pi fun k => ?_
  unfold ept
  split_ifs
  · exact continuous_star.comp ((continuous_apply k.2.1).comp (continuous_apply k.1))
  · exact (continuous_apply k.2.1).comp (continuous_apply k.1)

theorem continuous_evX (P : PX m n) : Continuous fun x : Fin m → Fin n → ℂ => evX P x :=
  (MvPolynomial.continuous_eval P).comp continuous_ept

theorem poly_bound (P : PX m n) : ∃ C : ℝ, ∃ k : ℕ, 0 ≤ C ∧ ∀ x, ‖evX P x‖ ≤ C * (1 + ‖x‖) ^ k := by
  induction P using MvPolynomial.induction_on with
  | C a => exact ⟨‖a‖, 0, norm_nonneg _, fun x => by simp [evX_eq]⟩
  | add p q hp hq =>
    obtain ⟨C₁, k₁, h₁, hb₁⟩ := hp
    obtain ⟨C₂, k₂, h₂, hb₂⟩ := hq
    refine ⟨C₁ + C₂, k₁ + k₂, add_nonneg h₁ h₂, fun x => ?_⟩
    have h1 : (1 : ℝ) ≤ 1 + ‖x‖ := le_add_of_nonneg_right (norm_nonneg x)
    have e1 : (1 + ‖x‖) ^ k₁ ≤ (1 + ‖x‖) ^ (k₁ + k₂) := pow_le_pow_right₀ h1 (Nat.le_add_right _ _)
    have e2 : (1 + ‖x‖) ^ k₂ ≤ (1 + ‖x‖) ^ (k₁ + k₂) := pow_le_pow_right₀ h1 (Nat.le_add_left _ _)
    rw [evX_eq, map_add (f := _)]
    calc ‖eval (ept x) p + eval (ept x) q‖ ≤ ‖eval (ept x) p‖ + ‖eval (ept x) q‖ := norm_add_le _ _
      _ ≤ C₁ * (1 + ‖x‖) ^ k₁ + C₂ * (1 + ‖x‖) ^ k₂ := add_le_add (hb₁ x) (hb₂ x)
      _ ≤ C₁ * (1 + ‖x‖) ^ (k₁ + k₂) + C₂ * (1 + ‖x‖) ^ (k₁ + k₂) :=
          add_le_add (mul_le_mul_of_nonneg_left e1 h₁) (mul_le_mul_of_nonneg_left e2 h₂)
      _ = (C₁ + C₂) * (1 + ‖x‖) ^ (k₁ + k₂) := by ring
  | mul_X p i hp =>
    obtain ⟨C, k, h0, hb⟩ := hp
    refine ⟨C, k + 1, h0, fun x => ?_⟩
    rw [evX_eq, map_mul, eval_X, norm_mul, pow_succ, ← mul_assoc]
    exact mul_le_mul (hb x) ((norm_ept_le x i).trans (le_add_of_nonneg_left zero_le_one)) (norm_nonneg _)
      (mul_nonneg h0 (pow_nonneg (by positivity) _))

theorem sq_norm_le_sum (x : Fin m → Fin n → ℂ) : ‖x‖ ^ 2 ≤ ∑ a, ∑ j, ‖x a j‖ ^ 2 :=
  _root_.UpperTheory.Reformulated.B.Yhb3.main x

theorem decay (k : ℕ) (κ : ℝ) (hκ : 0 < κ) (r : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, 0 ≤ s → (1 + s) ^ k * Real.exp (-(κ * s ^ 2)) ≤ C * (1 + s) ^ (-r) := by
  obtain ⟨N, hN⟩ := exists_nat_ge ((k : ℝ) + r)
  refine ⟨2 ^ N * (1 + N.factorial / κ ^ N), by positivity, fun s hs => ?_⟩
  have h1 : (1 : ℝ) ≤ 1 + s := le_add_of_nonneg_right hs
  have hpos : 0 < 1 + s := by linarith
  have hE : 0 < Real.exp (-(κ * s ^ 2)) := Real.exp_pos _

  have hA : (1 + s) ^ N ≤ 2 ^ N * (1 + (s ^ 2) ^ N) := by
    rcases le_total s 1 with h | h
    · calc (1 + s) ^ N ≤ 2 ^ N := pow_le_pow_left₀ hpos.le (by linarith) N
        _ ≤ 2 ^ N * (1 + (s ^ 2) ^ N) := le_mul_of_one_le_right (by positivity)
            (le_add_of_nonneg_right (by positivity))
    · have : 1 + s ≤ 2 * s ^ 2 := by nlinarith
      calc (1 + s) ^ N ≤ (2 * s ^ 2) ^ N := pow_le_pow_left₀ hpos.le this N
        _ = 2 ^ N * (s ^ 2) ^ N := by rw [mul_pow]
        _ ≤ 2 ^ N * (1 + (s ^ 2) ^ N) := by nlinarith [pow_nonneg (by positivity : (0:ℝ) ≤ 2) N]
  have hB : (s ^ 2) ^ N * Real.exp (-(κ * s ^ 2)) ≤ N.factorial / κ ^ N := by
    have := Real.pow_div_factorial_le_exp (x := κ * s ^ 2) (by positivity) N
    rw [div_le_iff₀ (by positivity)] at this
    rw [le_div_iff₀ (by positivity)]
    have e : Real.exp (-(κ * s ^ 2)) * Real.exp (κ * s ^ 2) = 1 := by rw [← Real.exp_add]; simp
    calc (s ^ 2) ^ N * Real.exp (-(κ * s ^ 2)) * κ ^ N = (κ * s ^ 2) ^ N * Real.exp (-(κ * s ^ 2)) := by ring
      _ ≤ (Real.exp (κ * s ^ 2) * N.factorial) * Real.exp (-(κ * s ^ 2)) :=
          mul_le_mul_of_nonneg_right this hE.le
      _ = N.factorial := by rw [mul_comm (Real.exp _), mul_assoc, mul_comm (Real.exp _), e, mul_one]
  have hC : (1 + s) ^ N * Real.exp (-(κ * s ^ 2)) ≤ 2 ^ N * (1 + N.factorial / κ ^ N) := by
    calc (1 + s) ^ N * Real.exp (-(κ * s ^ 2)) ≤ 2 ^ N * (1 + (s ^ 2) ^ N) * Real.exp (-(κ * s ^ 2)) :=
          mul_le_mul_of_nonneg_right hA hE.le
      _ = 2 ^ N * (Real.exp (-(κ * s ^ 2)) + (s ^ 2) ^ N * Real.exp (-(κ * s ^ 2))) := by ring
      _ ≤ 2 ^ N * (1 + N.factorial / κ ^ N) := by
          gcongr
          · exact Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg s])
  have hR : (1 + s) ^ k * (1 + s) ^ r ≤ (1 + s) ^ N := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hpos, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le h1 hN
  have hr : (1 + s) ^ r * (1 + s) ^ (-r) = 1 := by
    rw [← Real.rpow_add hpos]; simp
  calc (1 + s) ^ k * Real.exp (-(κ * s ^ 2))
      = ((1 + s) ^ k * (1 + s) ^ r * Real.exp (-(κ * s ^ 2))) * (1 + s) ^ (-r) := by
        rw [show ((1 + s) ^ k * (1 + s) ^ r * Real.exp (-(κ * s ^ 2))) * (1 + s) ^ (-r) =
          (1 + s) ^ k * Real.exp (-(κ * s ^ 2)) * ((1 + s) ^ r * (1 + s) ^ (-r)) by ring, hr, mul_one]
    _ ≤ ((1 + s) ^ N * Real.exp (-(κ * s ^ 2))) * (1 + s) ^ (-r) := by
        gcongr
    _ ≤ (2 ^ N * (1 + N.factorial / κ ^ N)) * (1 + s) ^ (-r) := by gcongr

end PositivityTheory.Rg.Sw.AbsSt.DF
end
end

noncomputable section

open MeasureTheory Matrix Set Filter Topology MvPolynomial

namespace PositivityTheory.Rg.Sw.AbsSt.DF

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

def scal (α : Fin n → ℝ) (x : Fin m → Fin n → ℂ) : Fin m → Fin n → ℂ := fun a j => (α j : ℂ) * x a j

def aH (X : Fin n → ℝ) (h : ℝ) : Fin n → ℝ := fun j => Real.exp (h * X j)

theorem ept_scal (α : Fin n → ℝ) (x : Fin m → Fin n → ℂ) :
    ept (scal α x) = fun k => (α k.2.1 : ℂ) * ept x k := by
  funext k
  unfold ept scal
  split_ifs
  · simp [star_mul', Complex.conj_ofReal]
  · rfl

theorem hasDerivAt_eval_curve {σ : Type*} [Fintype σ] [DecidableEq σ] (Q : MvPolynomial σ ℂ) (w : ℝ → σ → ℂ)
    (w' : σ → ℂ) (h : ℝ) (hw : ∀ k, HasDerivAt (fun s => w s k) (w' k) h) :
    HasDerivAt (fun s => eval (w s) Q) (∑ k, eval (w h) (pderiv k Q) * w' k) h := by
  induction Q using MvPolynomial.induction_on with
  | C a => simpa using hasDerivAt_const h a
  | add p q hp hq =>
    have e : (∑ k, eval (w h) (pderiv k (p + q)) * w' k) =
        (∑ k, eval (w h) (pderiv k p) * w' k) + ∑ k, eval (w h) (pderiv k q) * w' k := by
      simp [map_add (f := _), add_mul, Finset.sum_add_distrib]
    rw [e]
    exact (hp.add hq).congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => by simp)
  | mul_X p i hp =>
    have e : ∑ k, eval (w h) (pderiv k (p * X i)) * w' k =
        (∑ k, eval (w h) (pderiv k p) * w' k) * w h i + eval (w h) p * w' i := by
      have e1 : ∀ k, eval (w h) (pderiv k (p * X i)) * w' k =
          eval (w h) (pderiv k p) * w' k * w h i + (if k = i then eval (w h) p * w' i else 0) := by
        intro k
        rw [Derivation.leibniz, pderiv_X, smul_eq_mul, smul_eq_mul, map_add (f := _), map_mul, map_mul, eval_X]
        by_cases hk : k = i
        · subst hk; simp; ring
        · simp [Pi.single_apply, hk]; ring
      simp only [e1, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_mul]
    rw [e]
    exact (hp.mul (hw i)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => by simp)

theorem hasDerivAt_scal_coord (X : Fin n → ℝ) (y : Fin m → Fin n → ℂ) (h : ℝ) (k : Fin m × Fin n × Bool) :
    HasDerivAt (fun s => ept (scal (aH X s) y) k) ((X k.2.1 : ℂ) * ept (scal (aH X h) y) k) h := by
  simp only [ept_scal, aH]
  have h1 : HasDerivAt (fun s : ℝ => Real.exp (s * X k.2.1)) (Real.exp (h * X k.2.1) * X k.2.1) h := by
    simpa using ((hasDerivAt_id h).mul_const (X k.2.1)).exp
  have h2 := (h1.ofReal_comp).mul_const (ept y k)
  refine h2.congr_deriv ?_
  rw [Complex.ofReal_mul]; ring

theorem integral_scal (α : Fin n → ℝ) (hα : ∀ j, 0 < α j) (f : (Fin m → Fin n → ℂ) → ℂ) :
    ∫ x, f x = (∏ j, α j ^ (2 * m) : ℝ) * ∫ y, f (scal α y) := by
  let Li : (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℂ) := LinearMap.pi fun j => (α j • LinearMap.id).comp (LinearMap.proj j)
  let L : (Fin m → Fin n → ℂ) →ₗ[ℝ] (Fin m → Fin n → ℂ) := LinearMap.pi fun a => Li.comp (LinearMap.proj a)
  have hL : ∀ y, L y = scal α y := by
    intro y; funext a j; simp [L, Li, scal, Complex.real_smul]
  have hdetLi : LinearMap.det Li = ∏ j, α j ^ 2 := by
    simp only [Li, LinearMap.det_pi, LinearMap.det_smul, LinearMap.det_id, Complex.finrank_real_complex, mul_one]
  have hdet : LinearMap.det L = ∏ j, α j ^ (2 * m) := by
    simp only [L, LinearMap.det_pi, hdetLi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun j _ => by rw [← pow_mul, mul_comm]
  have hD : 0 < ∏ j, α j ^ (2 * m) := Finset.prod_pos fun j _ => pow_pos (hα j) _
  let Linv : (Fin m → Fin n → ℂ) →ₗ[ℝ] (Fin m → Fin n → ℂ) := LinearMap.pi fun a =>
    (LinearMap.pi fun j => ((α j)⁻¹ • LinearMap.id).comp (LinearMap.proj j)).comp (LinearMap.proj a)
  let Le : (Fin m → Fin n → ℂ) ≃ₗ[ℝ] (Fin m → Fin n → ℂ) := LinearEquiv.ofLinear L Linv
    (LinearMap.ext fun y => funext fun a => funext fun j => by
      have h0 : (α j : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hα j).ne'
      simp only [L, Li, Linv, LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.proj_apply, LinearMap.smul_apply,
        LinearMap.id_apply, LinearMap.id_coe, id_eq, Complex.real_smul, Complex.ofReal_inv]
      field_simp)
    (LinearMap.ext fun y => funext fun a => funext fun j => by
      have h0 : (α j : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hα j).ne'
      simp only [L, Li, Linv, LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.proj_apply, LinearMap.smul_apply,
        LinearMap.id_apply, LinearMap.id_coe, id_eq, Complex.real_smul, Complex.ofReal_inv]
      field_simp)
  have hH1 : (volume : Measure (Fin n → ℂ)).IsAddHaarMeasure := by infer_instance
  have hH2 : (volume : Measure (Fin m → Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  let e := Le.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  have he : ∀ y, e y = scal α y := fun y => hL y
  have hmap : Measure.map e (volume : Measure (Fin m → Fin n → ℂ)) =
      ENNReal.ofReal |(LinearMap.det L)⁻¹| • volume := by
    have : (e : (Fin m → Fin n → ℂ) → (Fin m → Fin n → ℂ)) = L := by funext y; rfl
    rw [this]
    exact Measure.map_linearMap_addHaar_eq_smul_addHaar volume (by rw [hdet]; exact hD.ne')
  have h1 : ∫ y, f (scal α y) = (∏ j, α j ^ (2 * m))⁻¹ * ∫ x, f x := by
    have := integral_map_equiv e f (μ := volume)
    simp only [he] at this
    rw [← this, hmap, integral_smul_measure, hdet, ENNReal.toReal_ofReal (abs_nonneg _),
      abs_of_pos (inv_pos.2 hD)]
    simp [Complex.real_smul]
  rw [h1, ← mul_assoc]
  push_cast
  rw [mul_inv_cancel₀ (by exact_mod_cast hD.ne'), one_mul]

end PositivityTheory.Rg.Sw.AbsSt.DF
end
end

noncomputable section

open MeasureTheory Matrix Set Filter Topology MvPolynomial

namespace PositivityTheory.Rg.Sw.AbsSt.DF

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

theorem gramX_apply (ε : Fin m → Bool) (x : Fin m → Fin n → ℂ) (i j : Fin n) :
    gramX ε x i j = ∑ a, sgn ε a * (star (x a i) * x a j) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [gramX, Qp, Qb, evX, map_sub, map_sum, map_mul, eval_X, Finset.sum_filter, if_true]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  cases h : ε a <;> simp [sgn, h]

theorem gramX_scal (ε : Fin m → Bool) (α : Fin n → ℝ) (x : Fin m → Fin n → ℂ) :
    gramX ε (scal α x) = diagonal (fun j => (α j : ℂ)) * gramX ε x * diagonal (fun j => (α j : ℂ)) := by
  ext i j
  simp only [gramX_apply, mul_diagonal, diagonal_mul, scal, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  simp only [star_mul', Complex.star_def, Complex.conj_ofReal]
  ring

theorem gramX_herm (ε : Fin m → Bool) (x : Fin m → Fin n → ℂ) : (gramX ε x)ᴴ = gramX ε x := by
  ext i j
  simp only [conjTranspose_apply, gramX_apply, star_sum, star_mul', star_star]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  cases h : ε a <;> simp [sgn, h, mul_comm]

theorem trace_im (ε : Fin m → Bool) (x : Fin m → Fin n → ℂ) {b : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsHermitian) :
    ((b * gramX ε x).trace).im = 0 := by
  have hG := gramX_herm ε x
  have h1 : star ((b * gramX ε x).trace) = (b * gramX ε x).trace := by
    rw [← trace_conjTranspose, conjTranspose_mul, hG, hb.eq, trace_mul_comm]
  have h2 := congrArg Complex.im h1
  simp only [Complex.star_def, Complex.conj_im] at h2
  linarith

theorem norm_phase (t : ℝ) (z : ℂ) (hz : z.im = 0) : ‖Complex.exp (Complex.I * t * z)‖ = 1 := by
  rw [Complex.norm_exp]
  simp [Complex.mul_re, Complex.mul_im, hz]

theorem trace_scal (ε : Fin m → Bool) (X : Fin n → ℝ) (h : ℝ) (b : Matrix (Fin n) (Fin n) ℂ) (y : Fin m → Fin n → ℂ) :
    (bS X h b * gramX ε (scal (aH X h) y)).trace = (b * gramX ε y).trace := by
  rw [gramX_scal]
  simp only [bS]
  set A : Matrix (Fin n) (Fin n) ℂ := diagonal fun j => ((Real.exp (-(h * X j)) : ℝ) : ℂ)
  set B : Matrix (Fin n) (Fin n) ℂ := diagonal fun j => ((aH X h j : ℝ) : ℂ)
  have hAB : A * B = 1 := by
    simp only [A, B, diagonal_mul_diagonal, aH]
    rw [← diagonal_one]
    congr 1
    funext j
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    simp
  have hBA : B * A = 1 := by
    simp only [A, B, diagonal_mul_diagonal, aH]
    rw [← diagonal_one]
    congr 1
    funext j
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    simp
  rw [show A * b * A * (B * gramX ε y * B) = A * (b * ((A * B) * gramX ε y * B)) by
    simp only [mul_assoc], hAB, one_mul, trace_mul_comm,
    show b * (gramX ε y * B) * A = b * gramX ε y * (B * A) by simp only [mul_assoc], hBA, mul_one]

theorem ept_true (v : Fin m → Fin n → ℂ) (a : Fin m) (j : Fin n) : ept v (a, j, true) = star (v a j) := rfl
theorem ept_false (v : Fin m → Fin n → ℂ) (a : Fin m) (j : Fin n) : ept v (a, j, false) = v a j := rfl

theorem evX_dil (c : ℝ) (X : Fin n → ℝ) (Q : PX m n) (v : Fin m → Fin n → ℂ) :
    evX (dil c X Q) v = ((m : ℂ) * ∑ j, (X j : ℂ)) * evX Q v +
      ∑ k, eval (ept v) (pderiv k Q) * ((X k.2.1 : ℂ) * ept v k) -
      (c : ℂ) * (∑ a, ∑ j, 2 * (X j : ℂ) * ((‖v a j‖ ^ 2 : ℝ) : ℂ)) * evX Q v := by
  have hn : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = star z * z := by
    intro z
    rw [Complex.star_def, Complex.conj_mul']
    push_cast
    ring
  have key : ∀ a b c d a' b' c' d' : ℂ, a = a' → b = c' → c = b' → d = d' →
      a + (b + c - d) = a' + (b' + c') - d' := by
    intros
    subst_vars
    ring
  show eval (ept v) (dil c X Q) = ((m : ℂ) * ∑ j, (X j : ℂ)) * eval (ept v) Q +
      ∑ k, eval (ept v) (pderiv k Q) * ((X k.2.1 : ℂ) * ept v k) -
      (c : ℂ) * (∑ a, ∑ j, 2 * (X j : ℂ) * ((‖v a j‖ ^ 2 : ℝ) : ℂ)) * eval (ept v) Q
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dil, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.add_apply,
    LinearMap.sub_apply, LinearMap.id_apply, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.mulLeft_apply, MvPolynomial.smul_eq_C_mul, nsmul_eq_mul, map_sum, map_add, map_sub,
    map_mul, eval_X, eval_C, map_natCast, ept_true, ept_false, Derivation.coeFn_coe, hn]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, ept_true, ept_false]
  rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin m))), Finset.sum_comm (s := (Finset.univ : Finset (Fin m)))]
  simp only [Finset.mul_sum, Finset.sum_mul, mul_add, add_mul, mul_sub, sub_mul, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  apply key
  · exact Finset.sum_congr rfl (fun _ _ => by ring)
  · exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))
  · exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))
  · exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))

end PositivityTheory.Rg.Sw.AbsSt.DF
