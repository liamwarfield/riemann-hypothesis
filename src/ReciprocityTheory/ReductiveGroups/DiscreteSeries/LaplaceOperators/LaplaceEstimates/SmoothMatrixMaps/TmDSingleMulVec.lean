module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.PsiDatumStatement
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.LholClmEventually

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.SmoothMatrixMaps.TmAContDiffMulLeft
noncomputable section

open Matrix
open scoped ContDiff InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open ReciprocityTheory.ChartRestriction.DS

section Calc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {ε : Fin n → Bool}

theorem tmA_eword_congr {f h : Matrix (Fin n) (Fin n) ℂ → ℂ} (e : ∀ x, Formalism.REAL.inUJ ε x → f x = h x) :
    ∀ (w : List (Fin n × Fin n)) (g : Matrix (Fin n) (Fin n) ℂ), Formalism.REAL.inUJ ε g →
      Formalism.REAL.Eword ε w f g = Formalism.REAL.Eword ε w h g
  | [], g, hg => e g hg
  | p :: w, g, hg => by
      simp only [Formalism.REAL.Eword]
      exact Formalism.REAL.lie_derivative_congr p.1 p.2 (fun x hx => tmA_eword_congr e w x hx) hg

theorem tmA_eword_lin {f h : Matrix (Fin n) (Fin n) ℂ → ℂ} (hf : Formalism.REAL.SmoothOnG ε f)
    (hh : Formalism.REAL.SmoothOnG ε h) (c : ℂ) :
    ∀ (w : List (Fin n × Fin n)) (g : Matrix (Fin n) (Fin n) ℂ), Formalism.REAL.inUJ ε g →
      Formalism.REAL.Eword ε w (fun x => f x + c * h x) g = Formalism.REAL.Eword ε w f g + c * Formalism.REAL.Eword ε w h g
  | [], g, _ => rfl
  | p :: w, g, hg => by
      simp only [Formalism.REAL.Eword]
      rw [Formalism.REAL.lie_derivative_congr (h := fun x => Formalism.REAL.Eword ε w f x + c * Formalism.REAL.Eword ε w h x) p.1 p.2
        (fun x hx => tmA_eword_lin hf hh c w x hx) hg]
      exact Formalism.REAL.lie_derivative_add_smul p.1 p.2 c (Formalism.REAL.smooth_iterated_lie_derivative hf w) (Formalism.REAL.smooth_iterated_lie_derivative hh w) hg

theorem tmA_eword_zero :
    ∀ (w : List (Fin n × Fin n)) (g : Matrix (Fin n) (Fin n) ℂ), Formalism.REAL.inUJ ε g →
      Formalism.REAL.Eword ε w (fun _ => (0 : ℂ)) g = 0
  | [], _, _ => rfl
  | p :: w, g, hg => by
      simp only [Formalism.REAL.Eword]
      rw [Formalism.REAL.lie_derivative_congr (h := fun _ => (0 : ℂ)) p.1 p.2 (fun x hx => tmA_eword_zero w x hx) hg]
      exact Formalism.REAL.lie_derivative_const_zero _ _ _

theorem tmA_eword_left (x : Matrix (Fin n) (Fin n) ℂ) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) :
    ∀ w : List (Fin n × Fin n),
      Formalism.REAL.Eword ε w (fun g => f (x * g)) = fun g => Formalism.REAL.Eword ε w f (x * g)
  | [] => rfl
  | p :: w => by
      simp only [Formalism.REAL.Eword]
      rw [tmA_eword_left x f w]
      funext g
      simp only [Formalism.REAL.Eab, Formalism.REAL.Ec, Formalism.REAL.Rd, Matrix.mul_assoc]

theorem tmA_inUJ_mul {x g : Matrix (Fin n) (Fin n) ℂ} (hx : Formalism.REAL.inUJ ε x) (hg : Formalism.REAL.inUJ ε g) :
    Formalism.REAL.inUJ ε (x * g) := by
  unfold Formalism.REAL.inUJ at *
  rw [Matrix.conjTranspose_mul,
    show gᴴ * xᴴ * Formalism.REAL.Jm ε * (x * g) = gᴴ * (xᴴ * Formalism.REAL.Jm ε * x) * g by
      simp only [Matrix.mul_assoc], hx, hg]

theorem tmA_inv_eq {x : Matrix (Fin n) (Fin n) ℂ} (hx : Formalism.REAL.inUJ ε x) :
    x⁻¹ = Formalism.REAL.Jm ε * xᴴ * Formalism.REAL.Jm ε := by
  apply Matrix.inv_eq_left_inv
  unfold Formalism.REAL.inUJ at hx
  rw [show Formalism.REAL.Jm ε * xᴴ * Formalism.REAL.Jm ε * x = Formalism.REAL.Jm ε * (xᴴ * Formalism.REAL.Jm ε * x) by
    simp only [Matrix.mul_assoc], hx, Formalism.REAL.Jm_mul_self]

theorem tmA_mul_inv {x : Matrix (Fin n) (Fin n) ℂ} (hx : Formalism.REAL.inUJ ε x) : x * x⁻¹ = 1 := by
  have h : Formalism.REAL.Jm ε * xᴴ * Formalism.REAL.Jm ε * x = 1 := by
    unfold Formalism.REAL.inUJ at hx
    rw [show Formalism.REAL.Jm ε * xᴴ * Formalism.REAL.Jm ε * x = Formalism.REAL.Jm ε * (xᴴ * Formalism.REAL.Jm ε * x) by
      simp only [Matrix.mul_assoc], hx, Formalism.REAL.Jm_mul_self]
  exact Matrix.mul_nonsing_inv x (Matrix.isUnit_det_of_left_inverse h)

theorem tmA_inUJ_inv {x : Matrix (Fin n) (Fin n) ℂ} (hx : Formalism.REAL.inUJ ε x) : Formalism.REAL.inUJ ε x⁻¹ := by
  have h1 := tmA_mul_inv hx
  rw [tmA_inv_eq hx] at h1 ⊢
  unfold Formalism.REAL.inUJ
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Formalism.REAL.Jm_conjTranspose,
    Matrix.conjTranspose_conjTranspose]
  have hJJ : ∀ M : Matrix (Fin n) (Fin n) ℂ, Formalism.REAL.Jm ε * (Formalism.REAL.Jm ε * M) = M := fun M => by
    rw [← Matrix.mul_assoc, Formalism.REAL.Jm_mul_self, Matrix.one_mul]
  simp only [Matrix.mul_assoc] at h1 ⊢
  rw [hJJ, h1, Matrix.mul_one]

theorem tmA_contDiff_mulLeft (x : Matrix (Fin n) (Fin n) ℂ) :
    ContDiff ℝ ∞ (fun g : Matrix (Fin n) (Fin n) ℂ => x * g) := by
  refine contDiff_pi.mpr fun i => contDiff_pi.mpr fun j => ?_
  simp only [Matrix.mul_apply]
  exact ContDiff.sum fun k _ => contDiff_const.mul (contDiff_apply_apply (𝕜 := ℝ) (n := ∞) k j)

theorem tmA_sm_left {f : Matrix (Fin n) (Fin n) ℂ → ℂ} (hf : Formalism.REAL.SmoothOnG ε f)
    {x : Matrix (Fin n) (Fin n) ℂ} (hx : Formalism.REAL.inUJ ε x) : Formalism.REAL.SmoothOnG ε (fun g => f (x * g)) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf (x * g₀) (tmA_inUJ_mul hx hg₀)
  have hL := tmA_contDiff_mulLeft x
  refine ⟨(fun g => x * g) ⁻¹' U, fun g => F (x * g), hU.preimage hL.continuous, hgU, ?_, ?_⟩
  · exact hF.comp hL.contDiffOn (fun g hg => hg)
  · intro g hg hgJ
    exact hfF (x * g) hg (tmA_inUJ_mul hx hgJ)

theorem tmA_sm_sum {ι : Type*} (s : Finset ι) (F : ι → Matrix (Fin n) (Fin n) ℂ → ℂ)
    (hF : ∀ i ∈ s, Formalism.REAL.SmoothOnG ε (F i)) : Formalism.REAL.SmoothOnG ε (fun x => ∑ i ∈ s, F i x) := by
  first | exact UpperTheory.Reformulated.B.Qf26.tmA_sm_sum.{u_1} .. | (apply UpperTheory.Reformulated.B.Qf26.tmA_sm_sum.{u_1} <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qf26.tmA_sm_sum.{u_1} <;> assumption) | (apply @UpperTheory.Reformulated.B.Qf26.tmA_sm_sum.{u_1} <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qf26.tmA_sm_sum.{u_1} <;> assumption) | (apply @UpperTheory.Reformulated.B.Qf26.tmA_sm_sum.{u_1} <;> first | assumption | infer_instance)

theorem tmA_eab_sum {ι : Type*} (s : Finset ι) (F : ι → Matrix (Fin n) (Fin n) ℂ → ℂ)
    (hF : ∀ i ∈ s, Formalism.REAL.SmoothOnG ε (F i)) (a b : Fin n) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : Formalism.REAL.inUJ ε g) :
    Formalism.REAL.Eab ε a b (fun x => ∑ i ∈ s, F i x) g = ∑ i ∈ s, Formalism.REAL.Eab ε a b (F i) g := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Formalism.REAL.lie_derivative_const_zero (ε := ε) a b g
  | insert i s hi ih =>
      have hs : ∀ j ∈ s, Formalism.REAL.SmoothOnG ε (F j) := fun j hj => hF j (Finset.mem_insert_of_mem hj)
      have e : (fun x => ∑ j ∈ insert i s, F j x) = fun x => F i x + 1 * ∑ j ∈ s, F j x := by
        funext x; rw [Finset.sum_insert hi, one_mul]
      rw [e, Formalism.REAL.lie_derivative_add_smul a b 1 (hF i (Finset.mem_insert_self i s)) (tmA_sm_sum s F hs) hg,
        ih hs, one_mul, Finset.sum_insert hi]

end Calc

section Frob

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedRing
  Matrix.frobeniusNormedAlgebra

variable {n : ℕ}

theorem tmA_frob_eq (A : Matrix (Fin n) (Fin n) ℂ) : frob A = ‖A‖ := S7.sqrt_hs_frobVG A

theorem tmA_frob_mul (A B : Matrix (Fin n) (Fin n) ℂ) : frob (A * B) ≤ frob A * frob B := by
  rw [tmA_frob_eq, tmA_frob_eq, tmA_frob_eq]
  exact Matrix.frobenius_norm_mul A B

end Frob

section Gen

variable {n : ℕ} {ε : Fin n → Bool}

theorem tmA_entry_le_frob (g : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) : ‖g i j‖ ≤ frob g := by
  have h := Real.abs_le_sqrt (S7.hs_entry_leVG g i j)
  rw [abs_of_nonneg (norm_nonneg _)] at h
  exact h

theorem tmA_one_le_col {g : Matrix (Fin n) (Fin n) ℂ} (hg : Formalism.REAL.inUJ ε g) (a : Fin n) :
    1 ≤ ∑ i, ‖g i a‖ ^ 2 := by
  have h := congrFun (congrFun hg a) a
  have h1 : ‖(gᴴ * Formalism.REAL.Jm ε * g) a a‖ = 1 := by
    rw [h]; unfold Formalism.REAL.Jm; rw [Matrix.diagonal_apply_eq]; split_ifs <;> simp
  have h2 : ‖(gᴴ * Formalism.REAL.Jm ε * g) a a‖ ≤ ∑ i, ‖g i a‖ ^ 2 := by
    rw [Matrix.mul_apply]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    unfold Formalism.REAL.Jm
    rw [Matrix.mul_diagonal, norm_mul, norm_mul, Matrix.conjTranspose_apply, norm_star]
    split_ifs <;> simp [sq]
  linarith

theorem tmA_one_le_frob {g : Matrix (Fin n) (Fin n) ℂ} (hg : Formalism.REAL.inUJ ε g) (a : Fin n) : 1 ≤ frob g := by
  unfold frob
  rw [Real.one_le_sqrt]
  refine (tmA_one_le_col hg a).trans ?_
  rw [Finset.sum_comm]
  exact Finset.single_le_sum (f := fun j => ∑ i, ‖g i j‖ ^ 2)
    (fun j _ => Finset.sum_nonneg fun i _ => by positivity) (Finset.mem_univ a)

theorem tmA_frob_trans {x₀ g : Matrix (Fin n) (Fin n) ℂ} (hx₀ : Formalism.REAL.inUJ ε x₀) (hg : Formalism.REAL.inUJ ε g)
    (a₀ : Fin n) {a : ℝ} (ha : 0 ≤ a) : frob (x₀⁻¹ * g) ^ (-a) ≤ frob x₀ ^ a * frob g ^ (-a) := by
  have hX := tmA_one_le_frob hx₀ a₀
  have hG := tmA_one_le_frob hg a₀
  have hle : frob g ≤ frob x₀ * frob (x₀⁻¹ * g) := by
    calc frob g = frob (x₀ * (x₀⁻¹ * g)) := by rw [← Matrix.mul_assoc, tmA_mul_inv hx₀, Matrix.one_mul]
      _ ≤ _ := tmA_frob_mul _ _
  have hq : frob g / frob x₀ ≤ frob (x₀⁻¹ * g) := by
    rw [div_le_iff₀ (by linarith)]; linarith
  calc frob (x₀⁻¹ * g) ^ (-a) ≤ (frob g / frob x₀) ^ (-a) :=
        Real.rpow_le_rpow_of_nonpos (div_pos (by linarith) (by linarith)) hq (by linarith)
    _ = frob x₀ ^ a * frob g ^ (-a) := by
        rw [Real.div_rpow (by linarith) (by linarith), Real.rpow_neg (by linarith : (0:ℝ) ≤ frob x₀)]
        field_simp

end Gen

section Coef

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Mat k r → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ D}

theorem tmB_rd_coef (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) {x₀ g X : Mat k r}
    (hy : x₀⁻¹ * g ∈ UJset ε) (hX : inG ε X) (w : H) (m : D) :
    Formalism.REAL.Rd X (coefX σ x₀ w (m : H)) g = coefX σ x₀ w ((actM E X m : D) : H) g := by
  set L : H →L[ℝ] ℂ := ((innerSL ℂ w).comp (σ (x₀⁻¹ * g))).restrictScalars ℝ with hL
  have h1 : (fun t : ℝ => coefX σ x₀ w (m : H) (g * NormedSpace.exp ((t : ℂ) • X))) =
      fun t : ℝ => L (σ (NormedSpace.exp ((t : ℂ) • X)) (m : H)) := by
    funext t
    simp only [coefX, ← Matrix.mul_assoc]
    rw [hσ.1.2 _ hy _ (exp_smul_mem_UJset hX t)]
    simp [hL, innerSL_apply_apply]
  have h2 := (L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hD.deriv X hX m)).deriv
  simp only [Function.comp_def] at h2
  unfold Formalism.REAL.Rd
  rw [h1, h2]
  simp [hL, coefX, innerSL_apply_apply]

theorem tmB_eab_coef (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) {x₀ g : Mat k r}
    (hy : x₀⁻¹ * g ∈ UJset ε) (w : H) (m : D) (a b : Fin (2 * r + k + 1)) :
    Formalism.REAL.Eab ε a b (coefX σ x₀ w (m : H)) g = coefX σ x₀ w ((E a b m : D) : H) g := by
  rw [Formalism.REAL.lie_derivative_def,
    tmB_rd_coef (X := Formalism.REAL.cpart1 ε (Matrix.single a b 1)) hσ hD hy (Formalism.REAL.real_part_single_mem ε a b) w m,
    tmB_rd_coef (X := Formalism.REAL.cpart2 ε (Matrix.single a b 1)) hσ hD hy (Formalism.REAL.imaginary_part_single_mem ε a b) w m]
  have hZ := (Formalism.REAL.complex_parts_mem_lie_algebra_holds _ ε (Matrix.single a b 1)).2.2.1
  have key : E a b = actM E (Formalism.REAL.cpart1 ε (Matrix.single a b 1)) +
      Complex.I • actM E (Formalism.REAL.cpart2 ε (Matrix.single a b 1)) := by
    rw [← actM_single' E a b, ← actM_smul', ← actM_add', ← hZ]
  rw [key]
  simp [coefX]

end Coef

end ReciprocityTheory.ChartRestriction.DS.Lap
end
end

noncomputable section

open Matrix MeasureTheory
open scoped ContDiff InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open ReciprocityTheory.ChartRestriction.DS

section Good

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Mat k r → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ D}

def TmGood (ε : Fin (2 * r + k + 1) → Bool) (σ : Mat k r → (H →L[ℂ] H)) (x₀ : Mat k r) (w : H) (a : ℝ)
    (m : H) : Prop :=
  Formalism.REAL.SmoothOnG ε (coefX σ x₀ w m) ∧
    ∀ wd : List (Fin (2 * r + k + 1) × Fin (2 * r + k + 1)), ∃ C : ℝ, ∀ g ∈ UJset ε,
      ‖Formalism.REAL.Eword ε wd (coefX σ x₀ w m) g‖ ≤ C * frob g ^ (-a)

theorem tmC_good_add {x₀ : Mat k r} {w : H} {a : ℝ} {m m' : H} (hm : TmGood ε σ x₀ w a m)
    (hm' : TmGood ε σ x₀ w a m') (c : ℂ) : TmGood ε σ x₀ w a (m + c • m') := by
  have e : coefX σ x₀ w (m + c • m') = fun g => coefX σ x₀ w m g + c * coefX σ x₀ w m' g := by
    funext g; simp [coefX, inner_add_right, inner_smul_right]
  refine ⟨?_, fun wd => ?_⟩
  · rw [e]; exact Formalism.REAL.smooth_on_group_add hm.1 (Formalism.REAL.smooth_on_group_const_mul c hm'.1)
  · obtain ⟨C₁, h₁⟩ := hm.2 wd
    obtain ⟨C₂, h₂⟩ := hm'.2 wd
    refine ⟨C₁ + ‖c‖ * C₂, fun g hg => ?_⟩
    rw [e, tmA_eword_lin hm.1 hm'.1 c wd g hg]
    calc ‖Formalism.REAL.Eword ε wd (coefX σ x₀ w m) g + c * Formalism.REAL.Eword ε wd (coefX σ x₀ w m') g‖
        ≤ ‖Formalism.REAL.Eword ε wd (coefX σ x₀ w m) g‖ + ‖c‖ * ‖Formalism.REAL.Eword ε wd (coefX σ x₀ w m') g‖ := by
          refine (norm_add_le _ _).trans ?_; rw [norm_mul]
      _ ≤ C₁ * frob g ^ (-a) + ‖c‖ * (C₂ * frob g ^ (-a)) :=
          add_le_add (h₁ g hg) (mul_le_mul_of_nonneg_left (h₂ g hg) (norm_nonneg c))
      _ = (C₁ + ‖c‖ * C₂) * frob g ^ (-a) := by ring

theorem tmC_good_zero (x₀ : Mat k r) (w : H) (a : ℝ) : TmGood ε σ x₀ w a 0 := by
  have e : coefX σ x₀ w 0 = fun _ => (0 : ℂ) := by funext g; simp [coefX]
  refine ⟨?_, fun wd => ⟨0, fun g hg => ?_⟩⟩
  · rw [e]; exact Formalism.REAL.smooth_on_group_const_fun 0
  · rw [e, tmA_eword_zero wd g hg]; simp

def tmGoodSub (ε : Fin (2 * r + k + 1) → Bool) (σ : Mat k r → (H →L[ℂ] H)) (D : Submodule ℂ H) (x₀ : Mat k r)
    (w : H) (a : ℝ) : Submodule ℂ D where
  carrier := {m | TmGood ε σ x₀ w a ((m : D) : H)}
  zero_mem' := by simpa using tmC_good_zero (ε := ε) (σ := σ) x₀ w a
  add_mem' := fun {m m'} hm hm' => by
    have := tmC_good_add hm hm' 1
    simpa using this
  smul_mem' := fun c m hm => by
    have := tmC_good_add (tmC_good_zero x₀ w a) hm c
    simpa using this

theorem tmC_good_E (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) {x₀ : Mat k r}
    (hx₀ : x₀ ∈ UJset ε) (w : H) {a : ℝ} {m : D} (hm : TmGood ε σ x₀ w a (m : H))
    (a' b' : Fin (2 * r + k + 1)) : TmGood ε σ x₀ w a ((E a' b' m : D) : H) := by
  have e : ∀ g, Formalism.REAL.inUJ ε g →
      Formalism.REAL.Eab ε a' b' (coefX σ x₀ w (m : H)) g = coefX σ x₀ w ((E a' b' m : D) : H) g :=
    fun g hg => tmB_eab_coef hσ hD (tmA_inUJ_mul (tmA_inUJ_inv hx₀) hg) w m a' b'
  refine ⟨Formalism.REAL.smooth_on_group_congr (Formalism.REAL.smooth_lie_derivative a' b' hm.1) e, fun wd => ?_⟩
  obtain ⟨C, hC⟩ := hm.2 (wd ++ [(a', b')])
  refine ⟨C, fun g hg => ?_⟩
  have h3 := eword_append_Eab ε (coefX σ x₀ w (m : H)) (a', b') wd
  rw [← tmA_eword_congr e wd g hg, h3]
  exact hC g hg

theorem tmC_good_V {lam : Fin (2 * r + k + 1) → ℝ} {V : Submodule ℂ D} {T : S7.KType ε (lowK ε lam)}
    {μ : Fin (2 * r + k + 1) → ℤ} {ι : V ≃ₗ[ℂ] T.V} (hμ : S7.IsMu lam μ)
    (hcoef : ∀ g ∈ UJset ε, ∀ v v' : V,
      ⟪((v' : D) : H), σ g ((v : D) : H)⟫_ℂ = ⟪ι v', S7.PsiM T μ g (ι v)⟫_ℂ)
    {a : ℝ} (ha : 0 ≤ a)
    (hdec : ∀ (wd : List (Fin (2 * r + k + 1) × Fin (2 * r + k + 1))) (v₁ v₂ : T.V), ∃ C : ℝ, ∀ g ∈ UJset ε,
      ‖Formalism.REAL.Eword ε wd (fun y => ⟪v₂, S7.PsiM T μ y v₁⟫_ℂ) g‖ ≤ C * frob g ^ (-a))
    {x₀ : Mat k r} (hx₀ : x₀ ∈ UJset ε) (w v : V) : TmGood ε σ x₀ ((w : D) : H) a ((v : D) : H) := by
  set ψ : Mat k r → ℂ := fun y => ⟪ι w, S7.PsiM T μ y (ι v)⟫_ℂ with hψdef
  have e : ∀ g, Formalism.REAL.inUJ ε g → coefX σ x₀ ((w : D) : H) ((v : D) : H) g = ψ (x₀⁻¹ * g) :=
    fun g hg => hcoef _ (tmA_inUJ_mul (tmA_inUJ_inv hx₀) hg) v w
  have hψ : Formalism.REAL.SmoothOnG ε ψ := by
    intro g₀ hg₀
    obtain ⟨U, F, hU, hgU, hF, hfF⟩ := S7.psiM_smooth T μ hμ g₀ hg₀
    set Lc : (T.V →L[ℂ] T.V) →L[ℂ] ℂ := (innerSL ℂ (ι w)).comp (ContinuousLinearMap.apply ℂ T.V (ι v))
    refine ⟨U, fun z => Lc (F z), hU, hgU, (Lc.restrictScalars ℝ).contDiff.comp_contDiffOn hF, ?_⟩
    intro g hg hgJ
    simp [hψdef, Lc, hfF g hg hgJ, innerSL_apply_apply]
  refine ⟨Formalism.REAL.smooth_on_group_congr (tmA_sm_left hψ (tmA_inUJ_inv hx₀)) (fun g hg => (e g hg).symm),
    fun wd => ?_⟩
  obtain ⟨C, hC⟩ := hdec wd (ι v) (ι w)
  obtain ⟨a₀⟩ : Nonempty (Fin (2 * r + k + 1)) := ⟨0⟩
  refine ⟨max C 0 * frob x₀ ^ a, fun g hg => ?_⟩
  have hy : x₀⁻¹ * g ∈ UJset ε := tmA_inUJ_mul (tmA_inUJ_inv hx₀) hg
  rw [tmA_eword_congr (h := fun g => ψ (x₀⁻¹ * g)) e wd g hg,
    congrFun (tmA_eword_left x₀⁻¹ ψ wd) g]
  have h1 := hC _ hy
  have h2 := tmA_frob_trans hx₀ hg a₀ ha
  have h3 : 0 ≤ frob (x₀⁻¹ * g) ^ (-a) := Real.rpow_nonneg (le_trans zero_le_one (tmA_one_le_frob hy a₀)) _
  calc ‖Formalism.REAL.Eword ε wd ψ (x₀⁻¹ * g)‖ ≤ max C 0 * frob (x₀⁻¹ * g) ^ (-a) :=
        h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) h3)
    _ ≤ max C 0 * (frob x₀ ^ a * frob g ^ (-a)) := mul_le_mul_of_nonneg_left h2 (le_max_right _ _)
    _ = max C 0 * frob x₀ ^ a * frob g ^ (-a) := by ring

theorem tmC_good_genSub (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) {lam : Fin (2 * r + k + 1) → ℝ}
    {V : Submodule ℂ D} {T : S7.KType ε (lowK ε lam)}
    {μ : Fin (2 * r + k + 1) → ℤ} {ι : V ≃ₗ[ℂ] T.V} (hμ : S7.IsMu lam μ)
    (hcoef : ∀ g ∈ UJset ε, ∀ v v' : V,
      ⟪((v' : D) : H), σ g ((v : D) : H)⟫_ℂ = ⟪ι v', S7.PsiM T μ g (ι v)⟫_ℂ)
    {a : ℝ} (ha : 0 ≤ a)
    (hdec : ∀ (wd : List (Fin (2 * r + k + 1) × Fin (2 * r + k + 1))) (v₁ v₂ : T.V), ∃ C : ℝ, ∀ g ∈ UJset ε,
      ‖Formalism.REAL.Eword ε wd (fun y => ⟪v₂, S7.PsiM T μ y v₁⟫_ℂ) g‖ ≤ C * frob g ^ (-a))
    {x₀ : Mat k r} (hx₀ : x₀ ∈ UJset ε) (w : V) {f : D} (hf : f ∈ genSub E V) :
    TmGood ε σ x₀ ((w : D) : H) a ((f : D) : H) := by
  have hle : genSub E V ≤ tmGoodSub ε σ D x₀ ((w : D) : H) a :=
    sInf_le ⟨fun v hv => tmC_good_V hμ hcoef ha hdec hx₀ w ⟨v, hv⟩,
      fun a' b' m hm => tmC_good_E hσ hD hx₀ _ hm a' b'⟩
  exact hle hf

end Good

section Mult

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool}

theorem tmD_cJ_lin (x₁ y y' : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (g : Mat k r) :
    cJ ε x₁ (y + c • y') g = cJ ε x₁ y g + c * cJ ε x₁ y' g := by
  simp [cJ, Formalism.QuantumDeterminants.herm, Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, dotProduct_smul]

theorem tmD_cJ_zero (x₁ : Fin (2 * r + k + 1) → ℂ) (g : Mat k r) : cJ ε x₁ 0 g = 0 := by
  simp [cJ, Formalism.QuantumDeterminants.herm]

def tmD_cJL (ε : Fin (2 * r + k + 1) → Bool) (x₁ y : Fin (2 * r + k + 1) → ℂ) : Mat k r →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun g => cJ ε x₁ y g
      map_add' := fun A B => by
        simp [cJ, Formalism.QuantumDeterminants.herm, Matrix.add_mulVec, Matrix.mulVec_add, dotProduct_add]
      map_smul' := fun c A => by
        simp only [cJ, Formalism.QuantumDeterminants.herm, RingHom.id_apply, Matrix.smul_mulVec, Matrix.mulVec_smul, dotProduct_smul,
          Complex.real_smul] }

theorem tmD_cJL_coe (x₁ y : Fin (2 * r + k + 1) → ℂ) : ⇑(tmD_cJL ε x₁ y) = cJ ε x₁ y := by
  ext g
  simp only [tmD_cJL, LinearMap.coe_toContinuousLinearMap']
  rfl

theorem tmD_cJ_smooth (x₁ y : Fin (2 * r + k + 1) → ℂ) : Formalism.REAL.SmoothOnG ε (cJ ε x₁ y) := by
  intro g₀ _
  refine ⟨Set.univ, ⇑(tmD_cJL ε x₁ y), isOpen_univ, Set.mem_univ _,
    (tmD_cJL ε x₁ y).contDiff.contDiffOn, fun g _ _ => by rw [tmD_cJL_coe]⟩

theorem tmD_rd_cJ (x₁ y : Fin (2 * r + k + 1) → ℂ) {X g : Mat k r} (hX : Formalism.REAL.inG ε X)
    (hg : Formalism.REAL.inUJ ε g) : Formalism.REAL.Rd X (cJ ε x₁ y) g = cJ ε x₁ (X *ᵥ y) g := by
  rw [Formalism.REAL.right_derivative_extends _ ε (cJ ε x₁ y) (⇑(tmD_cJL ε x₁ y)) Set.univ g X isOpen_univ (Set.mem_univ g) hg
    (tmD_cJL ε x₁ y).contDiff.contDiffOn (fun h _ _ => by rw [tmD_cJL_coe]) hX,
    ContinuousLinearMap.fderiv, tmD_cJL_coe]
  simp [cJ, Formalism.QuantumDeterminants.herm, Matrix.mulVec_mulVec]

theorem tmD_eab_cJ (x₁ y : Fin (2 * r + k + 1) → ℂ) (a b : Fin (2 * r + k + 1)) {g : Mat k r}
    (hg : Formalism.REAL.inUJ ε g) : Formalism.REAL.Eab ε a b (cJ ε x₁ y) g = cJ ε x₁ (Matrix.single a b 1 *ᵥ y) g := by
  rw [Formalism.REAL.lie_derivative_def, tmD_rd_cJ x₁ y (Formalism.REAL.real_part_single_mem ε a b) hg, tmD_rd_cJ x₁ y (Formalism.REAL.imaginary_part_single_mem ε a b) hg,
    ← tmD_cJ_lin]
  congr 1
  have hZ := (Formalism.REAL.complex_parts_mem_lie_algebra_holds _ ε (Matrix.single a b 1)).2.2.1
  rw [← Matrix.smul_mulVec, ← Matrix.add_mulVec, ← hZ]

theorem tmD_single_mulVec (a b c : Fin (2 * r + k + 1)) :
    Matrix.single a b (1 : ℂ) *ᵥ Pi.single c 1 = if c = b then Pi.single a 1 else 0 := by
  ext i
  by_cases hc : c = b
  · subst hc
    by_cases h : i = a
    · subst h; simp [Matrix.mulVec, dotProduct, Matrix.single_apply, Pi.single_apply]
    · simp [Matrix.mulVec, dotProduct, Matrix.single_apply, Pi.single_apply, h, Ne.symm h]
  · simp [Matrix.mulVec, dotProduct, Matrix.single_apply, Pi.single_apply, hc, Ne.symm hc]

theorem tmD_cJ_bound (x₁ : Fin (2 * r + k + 1) → ℂ) (c : Fin (2 * r + k + 1)) (g : Mat k r) :
    ‖cJ ε x₁ (Pi.single c 1) g‖ ≤ (∑ i, ‖x₁ i‖) * frob g := by
  unfold cJ Formalism.QuantumDeterminants.herm
  rw [dotProduct, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_mul, Pi.star_apply, norm_star]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have e : (Jm ε *ᵥ (g *ᵥ Pi.single c 1)) i = (if ε i then 1 else -1) * g i c := by
    rw [Jm, Matrix.mulVec_diagonal]
    congr 1
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [e, norm_mul]
  have := tmA_entry_le_frob g i c
  split_ifs <;> simpa using this

end Mult

end ReciprocityTheory.ChartRestriction.DS.Lap
