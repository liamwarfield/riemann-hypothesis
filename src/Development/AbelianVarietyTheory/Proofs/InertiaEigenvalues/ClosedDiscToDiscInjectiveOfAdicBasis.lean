module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosedDiscCoefficientsTopologicallyFree
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaussNormCoeffWittDisc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameAinfMatrixFrobeniusGaloisEqs

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinClosedDiscRestrictInjective
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinClosedDiscRestrictInjective
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem disc_restrict_injective : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ρ ρ' : ℝ≥0), 0 < ρ' → ρ' ≤ ρ →
    ρ < 1 → ∀ R : bk.DS ρ →+* bk.DS ρ', IsDiscMap (l := _) (u := _) (ρ := _) (RingHom.id bk.S) R → Function.Injective R := by
  intro l _ K bk ρ ρ' h0 hle h1 R hR
  have hρ0 : 0 < ρ := h0.trans_le hle
  obtain ⟨a, ha1, ha2, ha3, -⟩ := GlobalTheory.T.exists_gaussNorm_coeff_wittDisc l K bk ρ hρ0 h1
  obtain ⟨a', ha1', ha2', -, -⟩ := GlobalTheory.T.exists_gaussNorm_coeff_wittDisc l K bk ρ' h0 (hle.trans_lt h1)
  obtain ⟨-, -, hdense, -⟩ := GlobalTheory.T.closedDiscGaugeCompletion_basic_properties l bk.S (X : bk.S) ρ
  have htors : ∀ z : Disc l (0 : Wq l bk.a) 1, l • z = 0 → z = 0 := by
    intro z hz
    rw [nsmul_eq_mul] at hz
    exact ((isUnit_l_disc l (0 : Wq l bk.a) 1).mul_right_eq_zero).1 hz
  have hbound : ∀ (σ : ℝ≥0), 0 < σ → ∀ (b : bk.DS σ →+ Disc l (0 : Wq l bk.a) 1) (n : ℕ),
      (∀ y, ‖b y‖ * (σ : ℝ) ^ n ≤ ‖y‖) → ∀ y, ‖b y‖ ≤ ((σ : ℝ) ^ n)⁻¹ * ‖y‖ := by
    intro σ hσ b n hb y
    have hp : (0 : ℝ) < (σ : ℝ) ^ n := pow_pos (by exact_mod_cast hσ) n
    rw [inv_mul_eq_div, le_div_iff₀ hp]
    exact hb y
  have hcoef : ∀ n y, a' n (R y) = a n y := by
    intro n
    have e := hdense (Disc l (0 : Wq l bk.a) 1) htors ((a' n).comp R.toAddMonoidHom) (a n)
      (AddMonoidHomClass.continuous_of_bound _ (((ρ' : ℝ) ^ n)⁻¹) fun y =>
        (hbound ρ' h0 (a' n) n (ha2' n) (R y)).trans
          (mul_le_mul_of_nonneg_left (hR.norm_le y) (inv_nonneg.2 (by positivity))))
      (AddMonoidHomClass.continuous_of_bound _ (((ρ : ℝ) ^ n)⁻¹) (hbound ρ hρ0 (a n) n (ha2 n)))
      (fun x => by
        change a' n (R (toDisc l (X : bk.S) ρ x)) = a n (toDisc l (X : bk.S) ρ x)
        rw [hR.ext x, RingHom.id_apply, ha1', ha1])
    intro y
    exact DFunLike.congr_fun e y
  refine (injective_iff_map_eq_zero R).2 fun y hy => ?_
  have h := ha3 y 0 le_rfl fun n => by rw [← hcoef n y, hy, map_zero, norm_zero, zero_mul]
  exact norm_le_zero_iff.1 h

end GlobalTheory.BSP
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinClosedDiscRestrictInjectiveStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_closedDisc_restrict_injective : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ρ ρ' : ℝ≥0), 0 < ρ' → ρ' ≤ ρ → ρ < 1 → ∀ R : bk.DS ρ →+* bk.DS ρ', IsDiscMap (l := _) (u := _) (ρ := _) (RingHom.id bk.S) R → Function.Injective R := by
  first | exact @GlobalTheory.BSP.disc_restrict_injective | exact GlobalTheory.BSP.disc_restrict_injective | (intros; apply GlobalTheory.BSP.disc_restrict_injective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemBreuilKisinIdealPowOfNormLe
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemBreuilKisinIdealPowOfNormLe
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem exists_of_mem_ball_small {l : ℕ} (hl : 1 < l) {A : Type} [CommRing A] (u : A) {ρ : ℝ≥0} (h0 : 0 < ρ)
    (h1 : ρ < 1) (m n : ℕ) {y : PreDisc l u ρ} (hy : y ∈ ball l u ρ ((ρ : ℝ) ^ m / (l : ℝ) ^ n)) :
    ∃ (c : ℕ) (z₁ z₂ : A), algebraMap A (PreDisc l u ρ) ((l : A) ^ c) * y =
      algebraMap A (PreDisc l u ρ) (u ^ m * z₁ + (l : A) ^ (c + n) * z₂) := by
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl
  have hρ0 : (0 : ℝ) < ρ := h0
  have hρ1 : (ρ : ℝ) ≤ 1 := h1.le
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, b, c, hw, rfl⟩ := hx
    have e : algebraMap A (PreDisc l u ρ) ((l : A) ^ c) * (algebraMap A (PreDisc l u ρ) ((l : A) ^ a * u ^ b) *
        IsLocalization.Away.invSelf (l : A) ^ c) = algebraMap A (PreDisc l u ρ) ((l : A) ^ a * u ^ b) := by
      rw [map_pow, mul_left_comm, ← mul_pow, IsLocalization.Away.mul_invSelf, one_pow, mul_one]
    rcases le_or_gt m b with hb | hb
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hb
      refine ⟨c, (l : A) ^ a * u ^ k, 0, ?_⟩
      rw [e]; congr 1; ring
    · have hp : (ρ : ℝ) ^ m ≤ (ρ : ℝ) ^ b := pow_le_pow_of_le_one hρ0.le hρ1 hb.le
      have h2 : (l : ℝ) ^ (c + n) ≤ (l : ℝ) ^ a := by
        rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)] at hw
        have h3 : (l : ℝ) ^ (c + n) * (ρ : ℝ) ^ b ≤ (l : ℝ) ^ a * (ρ : ℝ) ^ b :=
          calc (l : ℝ) ^ (c + n) * (ρ : ℝ) ^ b = (l : ℝ) ^ c * (ρ : ℝ) ^ b * (l : ℝ) ^ n := by ring
            _ ≤ _ := hw
            _ ≤ (ρ : ℝ) ^ b * (l : ℝ) ^ a := mul_le_mul_of_nonneg_right hp (by positivity)
            _ = _ := mul_comm _ _
        exact le_of_mul_le_mul_right h3 (by positivity)
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ((pow_le_pow_iff_right₀ hl1).1 h2)
      refine ⟨c, 0, (l : A) ^ k * u ^ b, ?_⟩
      rw [e]; congr 1; ring
  | zero => exact ⟨0, 0, 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, z₁, z₂, h⟩ := hx
    obtain ⟨c', z₁', z₂', h'⟩ := hy
    refine ⟨c + c', (l : A) ^ c' * z₁ + (l : A) ^ c * z₁', z₂ + z₂', ?_⟩
    simp only [map_add (f := _), map_mul, map_pow, pow_add] at h h' ⊢
    linear_combination (algebraMap A (PreDisc l u ρ) (l : A)) ^ c' * h +
      (algebraMap A (PreDisc l u ρ) (l : A)) ^ c * h'
  | smul a x _ hx =>
    obtain ⟨c, z₁, z₂, h⟩ := hx
    refine ⟨c, a * z₁, a * z₂, ?_⟩
    simp only [map_add (f := _), map_mul, map_pow, pow_add, Algebra.smul_def] at h ⊢
    linear_combination (algebraMap A (PreDisc l u ρ) a) * h

theorem exists_of_norm_toDisc_lt {l : ℕ} (hl : 1 < l) {A : Type} [CommRing A] (u : A)
    (ht : ∀ x : A, (l : A) * x = 0 → x = 0) (m : ℕ) (hd : ∀ x y : A, (l : A) * x = u ^ m * y → u ^ m ∣ x)
    {ρ : ℝ≥0} (h0 : 0 < ρ) (h1 : ρ < 1) (n : ℕ) (x : A) (hx : ‖toDisc l u ρ x‖ < (ρ : ℝ) ^ m / (l : ℝ) ^ n) :
    ∃ z₁ z₂ : A, x = u ^ m * z₁ + (l : A) ^ n * z₂ := by
  have hb : algebraMap A (PreDisc l u ρ) x ∈ ball l u ρ ((ρ : ℝ) ^ m / (l : ℝ) ^ n) :=
    mem_ball_of_gauge_lt l u ρ ((norm_ofPre l u ρ _).symm.trans_lt hx)
  obtain ⟨c, z₁, z₂, h⟩ := exists_of_mem_ball_small hl u h0 h1 m n hb
  have hn : (l : A) ∈ nonZeroDivisors A := mem_nonZeroDivisors_iff_left.2 ht
  have hi : Function.Injective (algebraMap A (PreDisc l u ρ)) :=
    IsLocalization.injective (M := Submonoid.powers (l : A)) _ (Submonoid.powers_le.2 hn)
  rw [← map_mul] at h
  have h2 := hi h
  have key : ∀ (c : ℕ) (w : A), u ^ m ∣ (l : A) ^ c * w → u ^ m ∣ w := fun c => by
    induction c with
    | zero => intro w hw; simpa using hw
    | succ c ih =>
      rintro w ⟨y, hy⟩
      exact ih w (hd _ y (by rw [← hy]; ring))
  obtain ⟨z, hz⟩ := key c (x - (l : A) ^ n * z₂) ⟨z₁, by rw [pow_add] at h2; linear_combination h2⟩
  exact ⟨z, z₂, by linear_combination hz⟩

theorem BK.X_pow_natDegree_mem_J {l : ℕ} [Fact l.Prime] {K : FinExt l} (bk : BK K) :
    (X : bk.S) ^ bk.Ep.natDegree ∈ bk.J := by
  have h := congrArg (Polynomial.coeToPowerSeries.ringHom (R := Wq l bk.a)) bk.monic.as_sum
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_add (f := _), map_pow, map_sum, map_mul, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X,
    Polynomial.coe_C] at h
  have e : (X : bk.S) ^ bk.Ep.natDegree =
      bk.E - ∑ i ∈ Finset.range bk.Ep.natDegree, C (bk.Ep.coeff i) * (X : bk.S) ^ i := by
    rw [eq_sub_iff_add_eq]; exact h.symm
  rw [e]
  refine sub_mem (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)) (Ideal.mem_sup_left (sum_mem fun i hi => ?_))
  obtain ⟨w, hw⟩ := bk.dvd_coeff i (Finset.mem_range.1 hi)
  rw [hw, map_mul, map_natCast, mul_assoc]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

theorem mem_J_pow_of_norm_le : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A] (s : bk.S →+* A), (∀ x : A, (l : A) * x = 0 → x = 0) → (∀ (m : ℕ) (x y : A), (l : A) * x = s X ^ m * y → s X ^ m ∣ x) → ∀ (ρ : ℝ≥0), 0 < ρ → ρ < 1 → ∀ n : ℕ, ∃ r : ℝ, 0 < r ∧ ∀ x : A, ‖toDisc l (s X) ρ x‖ ≤ r → x ∈ (bk.J ^ n).map s := by
  intro l hl K bk A _ s ht hd ρ h0 h1 n
  have hl0 : (0 : ℝ) < l := Nat.cast_pos.2 hl.out.pos
  have hρ0 : (0 : ℝ) < ρ := h0
  have hr : 0 < (ρ : ℝ) ^ (bk.Ep.natDegree * n) / (l : ℝ) ^ n := by positivity
  refine ⟨_, half_pos hr, fun x hx => ?_⟩
  obtain ⟨z₁, z₂, rfl⟩ := exists_of_norm_toDisc_lt hl.out.one_lt (s X) ht _ (hd _) h0 h1 n x
    (hx.trans_lt (half_lt_self hr))
  refine add_mem (Ideal.mul_mem_right _ _ ?_) (Ideal.mul_mem_right _ _ ?_)
  · rw [← map_pow, pow_mul]
    exact Ideal.mem_map_of_mem _ (Ideal.pow_mem_pow bk.X_pow_natDegree_mem_J n)
  · rw [← map_natCast s, ← map_pow]
    exact Ideal.mem_map_of_mem _ (Ideal.pow_mem_pow (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)) n)

end GlobalTheory.BSP
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemBreuilKisinIdealPowOfNormLeStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_breuilKisinIdeal_pow_of_norm_le : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A] (s : bk.S →+* A), (∀ x : A, (l : A) * x = 0 → x = 0) → (∀ (m : ℕ) (x y : A), (l : A) * x = s X ^ m * y → s X ^ m ∣ x) → ∀ (ρ : ℝ≥0), 0 < ρ → ρ < 1 → ∀ n : ℕ, ∃ r : ℝ, 0 < r ∧ ∀ x : A, ‖toDisc l (s X) ρ x‖ ≤ r → x ∈ (bk.J ^ n).map s := by
  first | exact @GlobalTheory.BSP.mem_J_pow_of_norm_le | exact GlobalTheory.BSP.mem_J_pow_of_norm_le | (intros; apply GlobalTheory.BSP.mem_J_pow_of_norm_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosedDiscToDiscInjectiveOfAdicBasis
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem toDisc_injective_of_topBasis : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A]
    (s : bk.S →+* A) (ι : Type), TopBasis s bk.J ι → ∀ ρ : ℝ≥0, 0 < ρ → ρ < 1 →
    Function.Injective (toDisc l (s X) ρ) ∧
    (∀ n : ℕ, ∃ r : ℝ, 0 < r ∧ ∀ x : A, ‖toDisc l (s X) ρ x‖ ≤ r → x ∈ (bk.J ^ n).map s) ∧
    ∀ ρ' : ℝ≥0, 0 < ρ' → ρ' ≤ ρ → ∀ R : Disc l (s X) ρ →+* Disc l (s X) ρ', IsDiscMap (l := _) (u := _) (ρ := _) (RingHom.id A) R →
      Function.Injective R := by
  intro l _ K bk A _ s ι TB ρ hρ hρ1
  have hH : IsHausdorff bk.J bk.S := bk.complete.toIsHausdorff
  obtain ⟨-, -, -, -, h5⟩ := GlobalTheory.T.topologicalBasis_basic_facts bk.S A s bk.J ι TB hH
  have hlW : (l : Wq l bk.a) ≠ 0 := WittVector.p_nonzero l (Fq l bk.a)
  have hCl : (C (l : Wq l bk.a) : bk.S) = (l : bk.S) := map_natCast _ l
  have hlS0 : (l : bk.S) ≠ 0 := by
    rw [← hCl]; exact fun h => hlW (C_injective (h.trans (map_zero _).symm))
  have hlA : (l : A) ∈ nonZeroDivisors A := by
    simpa [map_natCast] using h5 _ (mem_nonZeroDivisors_of_ne_zero hlS0)
  have htor : ∀ x : A, (l : A) * x = 0 → x = 0 := fun x hx =>
    (mem_nonZeroDivisors_iff_right.1 hlA x) (by rw [mul_comm]; exact hx)
  have hdvd : ∀ (m : ℕ) (x y : A), (l : A) * x = s X ^ m * y → s X ^ m ∣ x := by
    intro m x y hxy
    rw [← map_pow, GlobalTheory.T.dvd_iff_dvd_coeff_breuilKisin l K bk A s ι TB]
    intro i
    have e := congrArg (TB.c i) hxy
    rw [← map_natCast s l, ← map_pow, TB.c_mul, TB.c_mul] at e
    have hd : X ^ m ∣ (l : bk.S) * TB.c i x := ⟨_, e⟩
    rw [PowerSeries.X_pow_dvd_iff] at hd ⊢
    intro k hk
    have := hd k hk
    rw [← hCl, coeff_C_mul] at this
    exact (mul_eq_zero.1 this).resolve_left hlW
  have small := GlobalTheory.T.mem_breuilKisinIdeal_pow_of_norm_le l K bk A s htor hdvd ρ hρ hρ1
  refine ⟨?_, small, ?_⟩
  · refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    have hmem : ∀ n : ℕ, x ∈ (bk.J.map s) ^ n := fun n => by
      obtain ⟨r, hr, h⟩ := small n
      rw [← Ideal.map_pow]
      exact h x (by rw [hx, norm_zero]; exact hr.le)
    have hHA : IsHausdorff (bk.J.map s) A := TB.complete.toIsHausdorff
    refine hHA.haus x fun n => ?_
    rw [SModEq.zero, Ideal.smul_eq_mul, Ideal.mul_top]
    exact hmem n
  · intro ρ' hρ' hρ'ρ R hR
    have hρ'1 : ρ' < 1 := lt_of_le_of_lt hρ'ρ hρ1
    have h1 : ‖toDisc l (s X) ρ (s X)‖ ≤ ρ := by
      simpa using norm_toDisc_pow_le (l := l) (u := s X) (ρ := ρ) 1 hρ
    have h1' : ‖toDisc l (s X) ρ' (s X)‖ ≤ ρ' := by
      simpa using norm_toDisc_pow_le (l := l) (u := s X) (ρ := ρ') 1 hρ'
    have h2 : ‖toDisc l (X : bk.S) ρ' (RingHom.id bk.S X)‖ ≤ ρ := by
      have := norm_toDisc_pow_le (l := l) (u := (X : bk.S)) (ρ := ρ') 1 hρ'
      simp only [pow_one] at this
      exact this.trans (by exact_mod_cast hρ'ρ)
    obtain ⟨cD, hc1, -, hcn, -, -, hsup, -, -⟩ :=
      GlobalTheory.T.closedDisc_coefficients_topologicallyFree l K bk A s ι TB ρ hρ hρ1 (Disc.map s h1) (isDiscMap_map s h1)
    obtain ⟨cD', hc1', -, hcn', -, -, -, -, -⟩ :=
      GlobalTheory.T.closedDisc_coefficients_topologicallyFree l K bk A s ι TB ρ' hρ' hρ'1 (Disc.map s h1') (isDiscMap_map s h1')
    set RS : bk.DS ρ →+* bk.DS ρ' := Disc.map (RingHom.id bk.S) h2 with hRS
    have hRSd : IsDiscMap (l := _) (u := _) (ρ := _) (RingHom.id bk.S) RS := isDiscMap_map _ h2
    have injS : Function.Injective RS := GlobalTheory.T.breuilKisin_closedDisc_restrict_injective l K bk ρ ρ' hρ' hρ'ρ hρ1 RS hRSd
    obtain ⟨-, hlnorm, -, -⟩ := GlobalTheory.T.closedDiscGaugeCompletion_basic_properties l bk.S (X : bk.S) ρ'
    obtain ⟨-, -, hext, -⟩ := GlobalTheory.T.closedDiscGaugeCompletion_basic_properties l A (s X) ρ
    have hlpos : (0 : ℝ) < l := Nat.cast_pos.2 (Fact.out : l.Prime).pos
    have htorD : ∀ z : bk.DS ρ', l • z = 0 → z = 0 := by
      intro z hz
      rw [nsmul_eq_mul] at hz
      have := hlnorm z
      rw [hz, norm_zero] at this
      exact norm_eq_zero.1 ((div_eq_zero_iff.1 this.symm).resolve_right hlpos.ne')
    have hRc : Continuous R :=
      AddMonoidHomClass.continuous_of_bound R 1 fun x => (hR.norm_le x).trans (one_mul _).ge
    have hRSc : Continuous RS :=
      AddMonoidHomClass.continuous_of_bound RS 1 fun x => (hRSd.norm_le x).trans (one_mul _).ge
    have key : ∀ i y, cD' i (R y) = RS (cD i y) := by
      intro i y
      have hF : Continuous ((cD' i).comp R.toAddMonoidHom) :=
        (AddMonoidHomClass.continuous_of_bound (cD' i) 1 fun z => (hcn' i z).trans (one_mul _).ge).comp hRc
      have hG : Continuous (RS.toAddMonoidHom.comp (cD i)) :=
        hRSc.comp (AddMonoidHomClass.continuous_of_bound (cD i) 1 fun z => (hcn i z).trans (one_mul _).ge)
      have := hext (bk.DS ρ') htorD ((cD' i).comp R.toAddMonoidHom) (RS.toAddMonoidHom.comp (cD i)) hF hG
        (fun a => by
          change cD' i (R (toDisc l (s X) ρ a)) = RS (cD i (toDisc l (s X) ρ a))
          rw [hR.ext, hc1, hc1', hRSd.ext]; rfl)
      exact DFunLike.congr_fun this y
    refine (injective_iff_map_eq_zero R).2 fun y hy => ?_
    have hz : ∀ i, cD i y = 0 := fun i =>
      injS (by rw [← key, hy, map_zero, map_zero])
    exact norm_le_zero_iff.1 (hsup y 0 le_rfl fun i => by rw [hz, norm_zero])

end GlobalTheory.BSP
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosedDiscToDiscInjectiveOfAdicBasisStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closedDisc_toDisc_injective_of_adicBasis : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A] (s : bk.S →+* A) (ι : Type), TopBasis s bk.J ι → ∀ ρ : ℝ≥0, 0 < ρ → ρ < 1 → Function.Injective (toDisc l (s X) ρ) ∧ (∀ n : ℕ, ∃ r : ℝ, 0 < r ∧ ∀ x : A, ‖toDisc l (s X) ρ x‖ ≤ r → x ∈ (bk.J ^ n).map s) ∧ ∀ ρ' : ℝ≥0, 0 < ρ' → ρ' ≤ ρ → ∀ R : Disc l (s X) ρ →+* Disc l (s X) ρ', IsDiscMap (l := _) (u := _) (ρ := _) (RingHom.id A) R → Function.Injective R := by
  first | exact @GlobalTheory.BSP.toDisc_injective_of_topBasis | exact GlobalTheory.BSP.toDisc_injective_of_topBasis | (intros; apply GlobalTheory.BSP.toDisc_injective_of_topBasis <;> assumption)
end
