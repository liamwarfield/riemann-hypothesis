module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.HidaSetting

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.CoefDTensActPow
section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.CoefCExpEntrySummable
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem coefC_pow_entry_le (B : Matrix (Fin n) (Fin n) ℂ) (j : ℕ) (c d : Fin n) :
    ‖(B ^ j) c d‖ ≤ (∑ a, ∑ b, ‖B a b‖) ^ j := by
  induction j generalizing c d with
  | zero =>
    simp only [pow_zero]
    by_cases h : c = d
    · subst h; simp
    · simp [Matrix.one_apply_ne h]
  | succ j ih =>
    rw [pow_succ, Matrix.mul_apply, pow_succ]
    have hN0 : 0 ≤ ∑ a, ∑ b, ‖B a b‖ := by positivity
    have hN : ∑ e, ‖B e d‖ ≤ ∑ a, ∑ b, ‖B a b‖ := by
      refine Finset.sum_le_sum fun e _ => ?_
      exact Finset.single_le_sum (f := fun b => ‖B e b‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ d)
    calc ‖∑ e, (B ^ j) c e * B e d‖ ≤ ∑ e, ‖(B ^ j) c e * B e d‖ := norm_sum_le _ _
      _ ≤ ∑ e, (∑ a, ∑ b, ‖B a b‖) ^ j * ‖B e d‖ := by
          refine Finset.sum_le_sum fun e _ => ?_
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right (ih c e) (norm_nonneg _)
      _ = (∑ a, ∑ b, ‖B a b‖) ^ j * ∑ e, ‖B e d‖ := by rw [Finset.mul_sum]
      _ ≤ (∑ a, ∑ b, ‖B a b‖) ^ j * ∑ a, ∑ b, ‖B a b‖ :=
          mul_le_mul_of_nonneg_left hN (pow_nonneg hN0 _)

theorem coefC_exp_entry_summable (B : Matrix (Fin n) (Fin n) ℂ) (s : ℝ) (c d : Fin n) :
    Summable fun j : ℕ => ‖(s : ℂ) ^ j / (j.factorial : ℂ) * (B ^ j) c d‖ := by
  refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_)
    (Real.summable_pow_div_factorial (‖(s : ℂ)‖ * ∑ a, ∑ b, ‖B a b‖))
  rw [norm_mul, norm_div, norm_pow, Complex.norm_natCast]
  calc ‖(s : ℂ)‖ ^ j / (j.factorial : ℝ) * ‖(B ^ j) c d‖
      ≤ ‖(s : ℂ)‖ ^ j / (j.factorial : ℝ) * (∑ a, ∑ b, ‖B a b‖) ^ j := by
        gcongr
        exact coefC_pow_entry_le B j c d
    _ = (‖(s : ℂ)‖ * ∑ a, ∑ b, ‖B a b‖) ^ j / (j.factorial : ℝ) := by ring

theorem coefC_exp_entry_hasSum (B : Matrix (Fin n) (Fin n) ℂ) (s : ℝ) (c d : Fin n) :
    HasSum (fun j : ℕ => (s : ℂ) ^ j / (j.factorial : ℂ) * (B ^ j) c d)
      ((NormedSpace.exp ((s : ℂ) • B)) c d) := by
  have hterm : ∀ j : ℕ, ((j.factorial : ℂ))⁻¹ • ((s : ℂ) • B) ^ j =
      fun c d => (s : ℂ) ^ j / (j.factorial : ℂ) * (B ^ j) c d := by
    intro j
    ext c d
    simp only [smul_pow, Matrix.smul_apply, smul_eq_mul]
    ring
  have hS : Summable fun j : ℕ => ((j.factorial : ℂ))⁻¹ • ((s : ℂ) • B) ^ j := by
    rw [show (fun j : ℕ => ((j.factorial : ℂ))⁻¹ • ((s : ℂ) • B) ^ j) =
      fun j : ℕ => (fun c d => (s : ℂ) ^ j / (j.factorial : ℂ) * (B ^ j) c d) from funext hterm]
    exact Pi.summable.mpr fun c => Pi.summable.mpr fun d => (coefC_exp_entry_summable B s c d).of_norm
  have hE : NormedSpace.exp ((s : ℂ) • B) = ∑' j : ℕ, ((j.factorial : ℂ))⁻¹ • ((s : ℂ) • B) ^ j := by
    rw [NormedSpace.exp_eq_tsum ℂ]
  have h2 := Pi.hasSum.mp (Pi.hasSum.mp hS.hasSum c) d
  rw [hE]
  convert h2 using 1
  funext j
  rw [hterm j]

theorem coefC_hasSum_mul {f g : ℕ → ℂ} {a b : ℂ} (hf : HasSum f a) (hg : HasSum g b)
    (hf' : Summable fun j => ‖f j‖) (hg' : Summable fun j => ‖g j‖) :
    HasSum (fun m => ∑ kl ∈ antidiagonal m, f kl.1 * g kl.2) (a * b) := by
  have hs := summable_norm_sum_mul_antidiagonal_of_summable_norm hf' hg'
  have h := (Summable.of_norm hs).hasSum
  rw [← tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf' hg', hf.tsum_eq, hg.tsum_eq] at h
  exact h

theorem coefC_choose_coef (s : ℂ) (j k : ℕ) :
    s ^ (j + k) / ((j + k).factorial : ℂ) * ((j + k).choose j : ℂ) =
      s ^ j / (j.factorial : ℂ) * (s ^ k / (k.factorial : ℂ)) := by
  have h1 : ((j + k).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h2 : (j.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h3 : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  rw [Nat.cast_choose ℂ (Nat.le_add_right j k), Nat.add_sub_cancel_left, pow_add]
  field_simp <;> ring

end ReciprocityTheory.ChartRestriction.DS
end
end

noncomputable section

open Finset
open scoped Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

def coefAm (dual : Bool) (g : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  cond dual (g⁻¹)ᵀ g

def coefBm (dual : Bool) (X : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  cond dual (-Xᵀ) X

theorem coefD_Am_exp (dual : Bool) (X : Matrix (Fin n) (Fin n) ℂ) (s : ℝ) :
    coefAm dual (NormedSpace.exp ((s : ℂ) • X)) = NormedSpace.exp ((s : ℂ) • coefBm dual X) := by
  cases dual
  · rfl
  · simp only [coefAm, coefBm, cond_true]
    rw [← Matrix.exp_neg, ← Matrix.exp_transpose]
    congr 1
    rw [Matrix.transpose_neg, Matrix.transpose_smul, smul_neg]

section Alg

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

def coefPm (B : Matrix (Fin n) (Fin n) ℂ) : Module.End ℂ (Fin n → M) :=
  LinearMap.pi fun c => ∑ d, B c d • LinearMap.proj d

theorem coefPm_apply (B : Matrix (Fin n) (Fin n) ℂ) (u : Fin n → M) (c : Fin n) :
    coefPm B u c = ∑ d, B c d • u d := by
  simp [coefPm, LinearMap.sum_apply]

theorem coefPm_pow (B : Matrix (Fin n) (Fin n) ℂ) (j : ℕ) (u : Fin n → M) (c : Fin n) :
    ((coefPm (M := M) B) ^ j) u c = ∑ d, (B ^ j) c d • u d := by
  induction j generalizing c with
  | zero =>
    simp only [pow_zero, Module.End.one_apply, Matrix.one_apply, ite_smul, one_smul, zero_smul]
    rw [Finset.sum_ite_eq]
    simp
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply, coefPm_apply, pow_succ']
    simp_rw [ih, Matrix.mul_apply, Finset.smul_sum, smul_smul, Finset.sum_smul]
    rw [Finset.sum_comm]

theorem coefD_diag_pow (A : Module.End ℂ M) (k : ℕ) (u : Fin n → M) (c : Fin n) :
    ((diagOp (n := n) A) ^ k) u c = (A ^ k) (u c) := by
  induction k generalizing u with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply, ih, diagOp_coord, ← Module.End.mul_apply, ← pow_succ]

theorem coefD_comm (A : Module.End ℂ M) (B : Matrix (Fin n) (Fin n) ℂ) :
    Commute (coefPm (M := M) B) (diagOp A) := by
  refine LinearMap.ext fun u => funext fun c => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Module.End.mul_apply, coefPm_apply, diagOp_coord, map_sum, map_smul]

theorem coefD_sum_ite (c : Fin n) (f : Fin n → Fin n → M) :
    ∑ x, ∑ y, (if c = x then f x y else 0) = ∑ y, f c y := by
  rw [Finset.sum_comm]
  simp [Finset.sum_ite_eq]

theorem coefD_sum_ite' (c : Fin n) (f : Fin n → Fin n → M) :
    ∑ x, ∑ y, (if c = y then f x y else 0) = ∑ x, f x c := by
  simp [Finset.sum_ite_eq]

theorem coefD_tensAct_eq (dual : Bool) (E : Fin n → Fin n → Module.End ℂ M)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    actM (tensF dual E) X = coefPm (coefBm dual X) + diagOp (actM E X) := by
  refine LinearMap.ext fun u => funext fun c => ?_
  simp only [actM, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply,
    Pi.smul_apply, coefPm_apply, diagOp_coord, Pi.add_apply]
  cases dual
  · simp only [tensF, cond_false, coefBm, tensV_coord, smul_add, Finset.sum_add_distrib, smul_ite,
      smul_zero, coefD_sum_ite]
    rw [add_comm]
  · simp only [tensF, cond_true, coefBm, tensVd_coord, smul_sub, Finset.sum_sub_distrib, smul_ite,
      smul_zero, coefD_sum_ite', Matrix.neg_apply, Matrix.transpose_apply, neg_smul,
      Finset.sum_neg_distrib]
    abel

theorem coefD_tensAct_pow (dual : Bool) (E : Fin n → Fin n → Module.End ℂ M)
    (X : Matrix (Fin n) (Fin n) ℂ) (m : ℕ) (u : Fin n → M) (c : Fin n) :
    ((actM (tensF dual E) X) ^ m) u c = ∑ kl ∈ antidiagonal m, (m.choose kl.1 : ℂ) •
      ∑ d, ((coefBm dual X) ^ kl.1) c d • ((actM E X) ^ kl.2) (u d) := by
  rw [coefD_tensAct_eq, (coefD_comm (actM E X) (coefBm dual X)).add_pow', LinearMap.sum_apply,
    Finset.sum_apply]
  refine Finset.sum_congr rfl fun kl _ => ?_
  rw [LinearMap.smul_apply, Pi.smul_apply, ← Nat.cast_smul_eq_nsmul ℂ, Module.End.mul_apply,
    coefPm_pow]
  simp_rw [coefD_diag_pow]

end Alg

section Rep

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D}

def coefTG (dual : Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (g : Matrix (Fin n) (Fin n) ℂ)
    (f : Fin n → H) : Fin n → H :=
  fun c => ∑ d, coefAm dual g c d • σ g (f d)

theorem coefD_tensGrp_eq (dual : Bool) (g : Matrix (Fin n) (Fin n) ℂ) (f : Fin n → H) (c : Fin n) :
    coefTG dual σ g f c = ∑ d, coefAm dual g c d • σ g (f d) := rfl

theorem coefD_comb (s : ℂ) (m : ℕ) (B : Matrix (Fin n) (Fin n) ℂ) (L : Fin n → Fin n → ℕ → ℂ) :
    s ^ m / (m.factorial : ℂ) * ∑ c, ∑ kl ∈ antidiagonal m, (m.choose kl.1 : ℂ) *
        ∑ d, (B ^ kl.1) c d * L c d kl.2 =
      ∑ c, ∑ d, ∑ kl ∈ antidiagonal m,
        s ^ kl.1 / (kl.1.factorial : ℂ) * (B ^ kl.1) c d * (s ^ kl.2 / (kl.2.factorial : ℂ) * L c d kl.2) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun kl hkl => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hkl
  rw [← mul_assoc, ← hkl, coefC_choose_coef, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  ring

theorem coefD_taylor (dual : Bool) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (Λ : (Fin n → H) →L[ℂ] ℂ) (w : Fin n → D) (s : ℝ)
    (hb : ∀ d, ∃ a : ℕ → ℝ, (∀ m, ‖((((actM E X) ^ m) (w d) : D) : H)‖ ≤ a m) ∧
      Summable fun m : ℕ => a m * |s| ^ m / (m.factorial : ℝ)) :
    HasSum (fun m : ℕ => (s : ℂ) ^ m / (m.factorial : ℂ) *
        Λ (fun c => ((((actM (tensF dual E) X) ^ m) w c : D) : H)))
      (Λ (coefTG dual σ (NormedSpace.exp ((s : ℂ) • X)) (fun d => ((w d : D) : H)))) := by
  set lc : Fin n → (H →L[ℂ] ℂ) := fun c => Λ.comp (ContinuousLinearMap.single ℂ (fun _ : Fin n => H) c)
  have hΛ : ∀ u : Fin n → H, Λ u = ∑ c, lc c (u c) := by
    intro u
    conv_lhs => rw [← Finset.univ_sum_single u]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    rfl
  set B := coefBm dual X
  set Y := actM E X
  set L : Fin n → Fin n → ℕ → ℂ := fun c d k => lc c ((((Y ^ k) (w d) : D) : H))

  have hpair : ∀ c d, HasSum (fun m => ∑ kl ∈ antidiagonal m,
      (s : ℂ) ^ kl.1 / (kl.1.factorial : ℂ) * (B ^ kl.1) c d * ((s : ℂ) ^ kl.2 / (kl.2.factorial : ℂ) * L c d kl.2))
      (coefAm dual (NormedSpace.exp ((s : ℂ) • X)) c d *
        lc c (σ (NormedSpace.exp ((s : ℂ) • X)) ((w d : D) : H))) := by
    intro c d
    obtain ⟨a, ha, hs⟩ := hb d
    have hA := coefC_exp_entry_hasSum B s c d
    rw [← coefD_Am_exp] at hA
    have hA' := coefC_exp_entry_summable B s c d
    have horb := hasSum_orbit_of_bound hσ hD hX (w d) a ha 0 s (by simpa using hs)
    rw [exp_zero_smul, hσ.1.1] at horb
    have horb' := horb.mapL (lc c)
    have hσs : HasSum (fun k : ℕ => (s : ℂ) ^ k / (k.factorial : ℂ) * L c d k)
        (lc c (σ (NormedSpace.exp ((s : ℂ) • X)) ((w d : D) : H))) := by
      refine horb'.congr_fun fun k => ?_
      simp only [L, Y, ContinuousLinearMap.one_apply, map_smul, smul_eq_mul, sub_zero]
      push_cast
      ring
    have hσ' : Summable fun k : ℕ => ‖(s : ℂ) ^ k / (k.factorial : ℂ) * L c d k‖ := by
      refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_) (hs.mul_left ‖lc c‖)
      rw [norm_mul, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, Complex.norm_natCast]
      have h1 : ‖L c d k‖ ≤ ‖lc c‖ * a k := ((lc c).le_opNorm _).trans
        (mul_le_mul_of_nonneg_left (ha k) (norm_nonneg _))
      calc |s| ^ k / (k.factorial : ℝ) * ‖L c d k‖ ≤ |s| ^ k / (k.factorial : ℝ) * (‖lc c‖ * a k) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = ‖lc c‖ * (a k * |s| ^ k / (k.factorial : ℝ)) := by ring
    have hmul := coefC_hasSum_mul hA hσs hA' hσ'
    exact hmul
  have htot := hasSum_sum fun c (_ : c ∈ (Finset.univ : Finset (Fin n))) =>
    hasSum_sum fun d (_ : d ∈ (Finset.univ : Finset (Fin n))) => hpair c d
  have hR : Λ (coefTG dual σ (NormedSpace.exp ((s : ℂ) • X)) (fun d => ((w d : D) : H))) =
      ∑ c, ∑ d, coefAm dual (NormedSpace.exp ((s : ℂ) • X)) c d *
        lc c (σ (NormedSpace.exp ((s : ℂ) • X)) ((w d : D) : H)) := by
    rw [hΛ]
    refine Finset.sum_congr rfl fun c _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [coefD_tensGrp_eq, map_sum]
    simp only [map_smul, smul_eq_mul]
  rw [hR]
  refine htot.congr_fun fun m => ?_
  rw [hΛ]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [coefD_tensAct_pow, Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul, smul_eq_mul]
  rw [← coefD_comb]

end Rep

end ReciprocityTheory.ChartRestriction.DS
end
end

noncomputable section

open Finset
open scoped Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section Rep

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D}

theorem coefE_Am_mul (dual : Bool) (g h : Matrix (Fin n) (Fin n) ℂ) :
    coefAm dual (g * h) = coefAm dual g * coefAm dual h := by
  cases dual <;> simp [coefAm, Matrix.mul_inv_rev, Matrix.transpose_mul]

theorem coefE_tensGrp_mul (dual : Bool) (hσ : IsURepOn (UJset ε) σ) {g h : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ UJset ε) (hh : h ∈ UJset ε) (w : Fin n → H) :
    coefTG dual σ (g * h) w = coefTG dual σ g (coefTG dual σ h w) := by
  ext c
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [coefTG, coefE_Am_mul, hσ.1.2 g hg h hh, ContinuousLinearMap.comp_apply, map_sum, map_smul,
    Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]

theorem coefE_tensGrp_one (dual : Bool) (hσ : IsURepOn (UJset ε) σ) (w : Fin n → H) :
    coefTG dual σ 1 w = w := by
  ext c
  cases dual <;> simp [coefTG, coefAm, hσ.1.1, Matrix.one_apply]

def coefLam (dual : Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (g : Matrix (Fin n) (Fin n) ℂ)
    (f : Fin n → H) : (Fin n → H) →L[ℂ] ℂ :=
  ∑ c, (innerSL ℂ (f c)).comp (∑ d, coefAm dual g c d • (σ g).comp (ContinuousLinearMap.proj d))

theorem coefLam_apply (dual : Bool) (g : Matrix (Fin n) (Fin n) ℂ) (f u : Fin n → H) :
    coefLam dual σ g f u = ∑ c, inner ℂ (f c) (coefTG dual σ g u c) := by
  simp [coefLam, coefTG, inner_sum, inner_smul_right]

def CoefGood (E : Fin n → Fin n → Module.End ℂ D) (V : Submodule ℂ D) (X : Matrix (Fin n) (Fin n) ℂ)
    (r₀ : ℝ) : Prop :=
  ∀ v ∈ genSub E V, ∃ a : ℕ → ℝ, (∀ m, ‖((((actM E X) ^ m) v : D) : H)‖ ≤ a m) ∧
    ∀ s : ℝ, |s| < r₀ → Summable fun m : ℕ => a m * |s| ^ m / (m.factorial : ℝ)

theorem coefE_goodP (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {V : Submodule ℂ D} (hVf : FiniteDimensional ℂ V) (hVK : IsKStableSub ε E V) {c : ℝ}
    (hc : ∀ v ∈ V, casimir E v = (c : ℂ) • v) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) :
    CoefGood E V X (1 / (√2 * √(∑ a, ∑ b, ‖X a b‖ ^ 2) + 1)) := by
  intro v hv
  obtain ⟨a, ha, -, hs⟩ := exists_orbit_bound hσ hD hVf hVK hc hX hv
  refine ⟨a, ha, fun s hs' => hs |s| (abs_nonneg s) ?_⟩
  have hA : 0 ≤ √2 * √(∑ a, ∑ b, ‖X a b‖ ^ 2) := by positivity
  rw [lt_div_iff₀ (by positivity)] at hs'
  nlinarith [abs_nonneg s]

theorem coefE_goodK (hD : IsDerivedOn ε σ D E)
    {V : Submodule ℂ D} (hVf : FiniteDimensional ℂ V) (hVK : IsKStableSub ε E V)
    {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : inK ε Z) (r₀ : ℝ) : CoefGood E V Z r₀ := by
  intro v hv
  obtain ⟨k, hk⟩ := exists_layer_of_mem_genSub hD.glRep hVK hv
  obtain ⟨C, -, hC⟩ := exists_norm_actM_pow_le_of_inK hD.glRep hVK hVf hZ k
  refine ⟨fun m => C ^ m * ‖v‖, fun m => hC v hk m, fun s _ => ?_⟩
  have := (Real.summable_pow_div_factorial (C * |s|)).mul_left ‖v‖
  exact this.congr fun m => by rw [mul_pow]; ring

theorem coefE_ι_act (dual : Bool) {V' : Submodule ℂ D} {ι : D →ₗ[ℂ] (Fin n → D)}
    (hιE : ∀ a b, ∀ x ∈ genSub E V', ι (E a b x) = tensF dual E a b (ι x))
    (X : Matrix (Fin n) (Fin n) ℂ) {v : D} (hv : v ∈ genSub E V') :
    ι (actM E X v) = actM (tensF dual E) X (ι v) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [actM, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul,
    hιE _ _ v hv]

private theorem actM_pow_apply_mem_genSub {M : Type*} [AddCommGroup M] [Module ℂ M]
    {E : Fin n → Fin n → Module.End ℂ M} {S : Submodule ℂ M} (X : Matrix (Fin n) (Fin n) ℂ) (m : ℕ)
    {v : M} (hv : v ∈ genSub E S) : ((actM E X) ^ m) v ∈ genSub E S := by
  have hE : ∀ a b, ∀ w ∈ genSub E S, E a b w ∈ genSub E S := by
    intro a b w hw
    simp only [genSub, Submodule.mem_sInf, Set.mem_setOf_eq] at hw ⊢
    intro T hT
    exact hT.2 a b w (hw T hT)
  induction m with
  | zero => simpa using hv
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply]
    simp only [actM, LinearMap.sum_apply, LinearMap.smul_apply]
    exact Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ =>
      Submodule.smul_mem _ _ (hE a b _ ih)

theorem coefE_ι_pow (dual : Bool) {V' : Submodule ℂ D} {ι : D →ₗ[ℂ] (Fin n → D)}
    (hιE : ∀ a b, ∀ x ∈ genSub E V', ι (E a b x) = tensF dual E a b (ι x))
    (X : Matrix (Fin n) (Fin n) ℂ) (m : ℕ) {y : D} (hy : y ∈ genSub E V') :
    ι (((actM E X) ^ m) y) = ((actM (tensF dual E) X) ^ m) (ι y) := by
  induction m generalizing y with
  | zero => simp
  | succ m ih =>
    have h1 : actM E X y ∈ genSub E V' := by simpa using actM_pow_apply_mem_genSub X 1 hy
    rw [pow_succ, Module.End.mul_apply, ih h1,
      coefE_ι_act dual hιE X hy, pow_succ, Module.End.mul_apply]

end Rep

section Propag

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D}

def CoefQ (dual : Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (E : Fin n → Fin n → Module.End ℂ D)
    (V' : Submodule ℂ D) (ι : D →ₗ[ℂ] (Fin n → D)) (f : Fin n → D) (z : D)
    (h : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ y ∈ genSub E V', ∑ c, inner ℂ ((f c : D) : H) (coefTG dual σ h (fun d => ((ι y d : D) : H)) c) =
    inner ℂ ((z : D) : H) (σ h ((y : D) : H))

theorem coefE_one_mem : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ UJset ε := by
  simp [UJset, inUJ]

theorem coefE_step (dual : Bool) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {V V' : Submodule ℂ D} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) {r₀ : ℝ}
    (hg : CoefGood E V X r₀) (hg' : CoefGood E V' X r₀) {ι : D →ₗ[ℂ] (Fin n → D)}
    (hι1 : ∀ x ∈ genSub E V', ι x ∈ tensSub (genSub E V))
    (hιE : ∀ a b, ∀ x ∈ genSub E V', ι (E a b x) = tensF dual E a b (ι x))
    (f : Fin n → D) (z : D) {h : Matrix (Fin n) (Fin n) ℂ} (hh : h ∈ UJset ε)
    (hQ : CoefQ dual σ E V' ι f z h) {s : ℝ} (hs : |s| < r₀) :
    CoefQ dual σ E V' ι f z (h * NormedSpace.exp ((s : ℂ) • X)) := by
  intro y hy
  have he : NormedSpace.exp ((s : ℂ) • X) ∈ UJset ε := rq_exp_mem ε X hX s

  have hL : HasSum (fun m : ℕ => (s : ℂ) ^ m / (m.factorial : ℂ) *
      coefLam dual σ h (fun c => ((f c : D) : H))
        (fun c => ((((actM (tensF dual E) X) ^ m) (ι y) c : D) : H)))
      (coefLam dual σ h (fun c => ((f c : D) : H))
        (coefTG dual σ (NormedSpace.exp ((s : ℂ) • X)) (fun d => ((ι y d : D) : H)))) := by
    apply coefD_taylor dual hσ hD hX
    intro d
    have hyd : ι y d ∈ genSub E V := by
      have := hι1 y hy
      simp only [tensSub, Submodule.mem_pi] at this
      exact this d (Set.mem_univ d)
    obtain ⟨a, ha, hsum⟩ := hg _ hyd
    exact ⟨a, ha, hsum s hs⟩

  obtain ⟨a', ha', hsum'⟩ := hg' y hy
  have hR0 := hasSum_orbit_of_bound hσ hD hX y a' ha' 0 s (by simpa using hsum' s hs)
  have h1 : σ (NormedSpace.exp (((0 : ℝ) : ℂ) • X)) = 1 := by
    simp [NormedSpace.exp_zero, hσ.1.1]
  simp only [h1, ContinuousLinearMap.one_apply] at hR0
  have hR := ((innerSL ℂ ((z : D) : H)).comp (σ h)).hasSum hR0
  have hterms : (fun m : ℕ => (s : ℂ) ^ m / (m.factorial : ℂ) *
      coefLam dual σ h (fun c => ((f c : D) : H))
        (fun c => ((((actM (tensF dual E) X) ^ m) (ι y) c : D) : H))) =
      fun m : ℕ => ((innerSL ℂ ((z : D) : H)).comp (σ h))
        ((((s - 0) ^ m / (m.factorial : ℝ) : ℝ) : ℂ) • ((((actM E X) ^ m) y : D) : H)) := by
    funext m
    rw [← coefE_ι_pow dual hιE X m hy, coefLam_apply,
      hQ _ (actM_pow_apply_mem_genSub X m hy)]
    simp [inner_smul_right]
  rw [hterms] at hL
  have key := hL.unique hR
  rw [coefLam_apply, ← coefE_tensGrp_mul dual hσ hh he] at key
  rw [hσ.1.2 h hh _ he]
  simpa using key

theorem coefE_line (dual : Bool) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {V V' : Submodule ℂ D} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hg : CoefGood E V X r₀) (hg' : CoefGood E V' X r₀) {ι : D →ₗ[ℂ] (Fin n → D)}
    (hι1 : ∀ x ∈ genSub E V', ι x ∈ tensSub (genSub E V))
    (hιE : ∀ a b, ∀ x ∈ genSub E V', ι (E a b x) = tensF dual E a b (ι x))
    (f : Fin n → D) (z : D) {h : Matrix (Fin n) (Fin n) ℂ} (hh : h ∈ UJset ε)
    (hQ : CoefQ dual σ E V' ι f z h) (t : ℝ) :
    CoefQ dual σ E V' ι f z (h * NormedSpace.exp ((t : ℂ) • X)) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (|t| / r₀)
  have hNpos : (0 : ℝ) < N := lt_of_le_of_lt (div_nonneg (abs_nonneg t) hr₀.le) hN
  have hs : |t / N| < r₀ := by
    rw [abs_div, Nat.abs_cast, div_lt_iff₀ hNpos]
    rw [div_lt_iff₀ hr₀] at hN
    linarith
  have key : ∀ k : ℕ, h * NormedSpace.exp (((k * (t / N) : ℝ) : ℂ) • X) ∈ UJset ε ∧
      CoefQ dual σ E V' ι f z (h * NormedSpace.exp (((k * (t / N) : ℝ) : ℂ) • X)) := by
    intro k
    induction k with
    | zero => simpa [NormedSpace.exp_zero] using ⟨hh, hQ⟩
    | succ k ih =>
      have hexp : NormedSpace.exp (((((k + 1 : ℕ) : ℝ) * (t / N) : ℝ) : ℂ) • X) =
          NormedSpace.exp (((k * (t / N) : ℝ) : ℂ) • X) * NormedSpace.exp (((t / N : ℝ) : ℂ) • X) := by
        rw [← Matrix.exp_add_of_commute]
        · congr 1
          push_cast
          rw [← add_smul]
          congr 1
          ring
        · exact ((Commute.refl X).smul_left _).smul_right _
      rw [hexp, ← mul_assoc]
      exact ⟨rq_UJ_mul ih.1 (rq_exp_mem ε X hX _),
        coefE_step dual hσ hD hX hg hg' hι1 hιE f z ih.1 ih.2 hs⟩
  have := (key N).2
  rwa [show ((N : ℝ) * (t / N)) = t by field_simp] at this

theorem coefE_all (dual : Bool) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {V V' : Submodule ℂ D} (hVf : FiniteDimensional ℂ V) (hVK : IsKStableSub ε E V) {c : ℝ}
    (hc : ∀ v ∈ V, casimir E v = (c : ℂ) • v) (hV'f : FiniteDimensional ℂ V')
    (hV'K : IsKStableSub ε E V') {c' : ℝ} (hc' : ∀ v ∈ V', casimir E v = (c' : ℂ) • v)
    {ι : D →ₗ[ℂ] (Fin n → D)}
    (hι1 : ∀ x ∈ genSub E V', ι x ∈ tensSub (genSub E V))
    (hιE : ∀ a b, ∀ x ∈ genSub E V', ι (E a b x) = tensF dual E a b (ι x))
    (f : Fin n → D) (z : D)
    (hz : ∀ y ∈ genSub E V', inner ℂ z y = ∑ c, inner ℂ (f c) (ι y c)) :
    ∀ g ∈ UJset ε, CoefQ dual σ E V' ι f z g := by
  intro g hg
  obtain ⟨k, hk, Y, hY, rfl⟩ := polar_UJ hg
  obtain ⟨Z, hZ, rfl⟩ := exists_exp_eq_of_mem_Kset hk

  have hQ1 : CoefQ dual σ E V' ι f z 1 := by
    intro y hy
    rw [coefE_tensGrp_one dual hσ, hσ.1.1, ContinuousLinearMap.one_apply]
    simp only [← Submodule.coe_inner]
    exact (hz y hy).symm

  have hZ1 := coefE_line dual hσ hD hZ.1 one_pos (coefE_goodK hD hVf hVK hZ 1)
    (coefE_goodK hD hV'f hV'K hZ 1) hι1 hιE f z coefE_one_mem hQ1 1
  simp only [one_mul, Complex.ofReal_one, one_smul] at hZ1

  have hr : 0 < 1 / (√2 * √(∑ a, ∑ b, ‖Y a b‖ ^ 2) + 1) := by positivity
  have hY1 := coefE_line dual hσ hD hY.1 hr (coefE_goodP hσ hD hVf hVK hc hY)
    (coefE_goodP hσ hD hV'f hV'K hc' hY) hι1 hιE f z (rq_K_UJ hk) hZ1 1
  simpa using hY1

end Propag

end ReciprocityTheory.ChartRestriction.DS
