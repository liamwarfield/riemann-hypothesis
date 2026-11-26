module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormGLIteratedDecayModerateGrowth
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPairDecomposition

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormRapidDecaySiegelConeRealPoints
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormGLUniformModerateGrowth
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WordEqSmoothingOfReproduced
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WordEqSmoothingOfReproduced
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

namespace GlobalTheory.AutGrowth

theorem word_eq_smoothing_of_reproduced : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure] (α : Lie E a → ℂ), IsTest (invSet E a) α → ∀ φ : Sm E a,
    smoothing ν α φ.1 = φ.1 → ∀ l : List (Lie E a), ∃ β : Lie E a → ℂ, IsTest (invSet E a) β ∧
      ((l.map (lie E a)).prod φ).1 = smoothing ν β φ.1 := by
  intro E _ _ _ a ν _ α hα φ hφ l
  induction l with
  | nil => exact ⟨α, hα, by simpa using hφ.symm⟩
  | cons X l ih =>
    obtain ⟨β, hβ, e⟩ := ih
    refine ⟨dens X β, isTest_dens X hβ, ?_⟩
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply]
    funext g
    change lieD X ((l.map (lie E a)).prod φ).1 g = _
    rw [e]
    exact lieD_smoothing ν hβ φ.2 X g

end GlobalTheory.AutGrowth
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WordEqSmoothingOfReproducedStatement
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_test_word_eq_smoothing : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure] (α : Lie E a → ℂ), IsTest (invSet E a) α → ∀ φ : Sm E a, smoothing ν α φ.1 = φ.1 → ∀ l : List (Lie E a), ∃ β : Lie E a → ℂ, IsTest (invSet E a) β ∧ ((l.map (lie E a)).prod φ).1 = smoothing ν β φ.1 := by
  first | exact @GlobalTheory.AutGrowth.word_eq_smoothing_of_reproduced | exact GlobalTheory.AutGrowth.word_eq_smoothing_of_reproduced | (intros; apply GlobalTheory.AutGrowth.word_eq_smoothing_of_reproduced <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothingGrowthExponent
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothingGrowthExponent
noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory Filter Topology

namespace GlobalTheory.AutGrowth

theorem smoothing_growth_exponent : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure] (α : Lie E a → ℂ), IsTest (invSet E a) α →
    ∀ (f : GA E a → ℂ) (C : ℝ) (N : ℕ), (∀ y, ‖f (infGL E a y)‖ ≤ C * height y ^ N) →
    ∃ C' : ℝ, ∀ y, ‖smoothing ν α f (infGL E a y)‖ ≤ C' * height y ^ N := by
  intro E _ _ _ a ν _ α hα f C N hC
  have C0 : 0 ≤ C := by
    have h1 := (norm_nonneg _).trans (hC 1)
    have hp : 0 < height (1 : GL (Fin a) (Cinf E)) ^ N :=
      pow_pos (by linarith [one_le_height (1 : GL (Fin a) (Cinf E))]) N
    exact nonneg_of_mul_nonneg_left h1 hp
  have hK : IsCompact (tsupport α) := hα.2.1
  obtain ⟨M, M0, hM⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ tsupport α, ‖x‖ ≤ M ∧ ‖toL (Matrix.of x)⁻¹‖ ≤ M := by
    obtain ⟨M1, h1⟩ := hK.exists_bound_of_continuousOn continuous_id.continuousOn
    obtain ⟨M2, h2⟩ := hK.exists_bound_of_continuousOn (continuousOn_toL_inv.mono hα.2.2)
    refine ⟨max 0 (max M1 M2), le_max_left _ _, fun x hx => ⟨?_, ?_⟩⟩
    · exact (h1 x hx).trans ((le_max_left _ _).trans (le_max_right _ _))
    · exact (h2 x hx).trans ((le_max_right _ _).trans (le_max_right _ _))
  set c : ℝ := 1 + a * M with hc
  have hc1 : 1 ≤ c := by
    have : 0 ≤ (a : ℝ) * M := by positivity
    linarith
  refine ⟨(∫ x, ‖α x‖ ∂ν) * C * c ^ N, fun y => ?_⟩
  have hb : ∀ x, ‖α x * chart f (infGL E a y) x‖ ≤ ‖α x‖ * (C * c ^ N * height y ^ N) := by
    intro x
    by_cases hx : x ∈ tsupport α
    · obtain ⟨u, hu⟩ : IsUnit (Matrix.of x) := hα.2.2 hx
      have hxu : x = toL u.val := by rw [hu]; rfl
      subst hxu
      obtain ⟨m1, m2⟩ := hM _ hx
      have m2' : ‖toL (u⁻¹).val‖ ≤ M := by rw [Matrix.coe_units_inv]; exact m2
      rw [norm_mul]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      rw [chart_val, ← map_mul]
      refine (hC (y * u)).trans ?_
      have hh : height (y * u) ≤ c * height y := by
        have e2 : ((y * u)⁻¹ : GL (Fin a) (Cinf E)).val = (u⁻¹).val * (y⁻¹).val := by
          rw [_root_.mul_inv_rev]; rfl
        have p1 := norm_toL_mul_le y.val u.val
        have p2 := norm_toL_mul_le (u⁻¹).val (y⁻¹).val
        have n1 := norm_nonneg (toL y.val)
        have n2 := norm_nonneg (toL (y⁻¹).val)
        have q1 : (a : ℝ) * (‖toL y.val‖ * ‖toL u.val‖) ≤ a * M * ‖toL y.val‖ := by
          calc (a : ℝ) * (‖toL y.val‖ * ‖toL u.val‖) ≤ a * (‖toL y.val‖ * M) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left m1 n1) (Nat.cast_nonneg a)
            _ = a * M * ‖toL y.val‖ := by ring
        have q2 : (a : ℝ) * (‖toL (u⁻¹).val‖ * ‖toL (y⁻¹).val‖) ≤ a * M * ‖toL (y⁻¹).val‖ := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left m2' (Nat.cast_nonneg a)) n2
        have aM : 0 ≤ (a : ℝ) * M := by positivity
        unfold height
        rw [show toL (y * u).val = toL (y.val * u.val) from rfl, e2, hc]
        nlinarith
      calc C * height (y * u) ^ N ≤ C * (c * height y) ^ N :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith [one_le_height (y * u)]) hh N) C0
        _ = C * c ^ N * height y ^ N := by rw [mul_pow, mul_assoc]
    · rw [image_eq_zero_of_notMem_tsupport hx]
      simp
  change ‖∫ x, α x * chart f (infGL E a y) x ∂ν‖ ≤ _
  have hi : Integrable (fun x => ‖α x‖) ν :=
    hα.1.continuous.norm.integrable_of_hasCompactSupport hα.2.1.norm
  refine (norm_integral_le_of_norm_le (hi.mul_const _) (.of_forall hb)).trans (le_of_eq ?_)
  rw [integral_mul_const]
  ring

end GlobalTheory.AutGrowth
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothingGrowthExponentStatement
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smoothing_norm_le_height_pow : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure] (α : Lie E a → ℂ), IsTest (invSet E a) α → ∀ (f : GA E a → ℂ) (C : ℝ) (N : ℕ), (∀ y, ‖f (infGL E a y)‖ ≤ C * height y ^ N) → ∃ C' : ℝ, ∀ y, ‖smoothing ν α f (infGL E a y)‖ ≤ C' * height y ^ N := by
  first | exact @GlobalTheory.AutGrowth.smoothing_growth_exponent | exact GlobalTheory.AutGrowth.smoothing_growth_exponent | (intros; apply GlobalTheory.AutGrowth.smoothing_growth_exponent <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormGLUniformModerateGrowth
noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

theorem GlobalTheory.AutGrowth.uniform_growth_of_autForm : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E]
    [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a), IsAutForm φ → ∃ N : ℕ, ∀ l : List (Lie E a),
    ∃ C : ℝ, ∀ y, ‖((l.map (lie E a)).prod φ).1 (infGL E a y)‖ ≤ C * height y ^ N := by
  intro hP E _ _ _ a φ hφ
  let ν : Measure (Lie E a) := Measure.addHaar
  obtain ⟨C, N, hC⟩ := hφ.growth 1
  simp only [one_mul] at hC
  obtain ⟨α, hα, hconv⟩ := GlobalTheory.T.automorphicForm_eq_own_realLieSmoothing hP E a ν φ hφ
  refine ⟨N, fun l => ?_⟩
  obtain ⟨β, hβ, hw⟩ := GlobalTheory.T.exists_test_word_eq_smoothing E a ν α hα φ hconv l
  obtain ⟨C', hC'⟩ := GlobalTheory.T.exists_smoothing_norm_le_height_pow E a ν β hβ φ.1 C N hC
  exact ⟨C', fun y => by rw [hw]; exact hC' y⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormGLUniformModerateGrowthStatement
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.automorphicForm_GL_uniform_moderate_growth : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a), IsAutForm φ → ∃ N : ℕ, ∀ l : List (Lie E a), ∃ C : ℝ, ∀ y, ‖((l.map (lie E a)).prod φ).1 (infGL E a y)‖ ≤ C * height y ^ N := by
  first | exact @GlobalTheory.AutGrowth.uniform_growth_of_autForm | exact GlobalTheory.AutGrowth.uniform_growth_of_autForm | (intros; apply GlobalTheory.AutGrowth.uniform_growth_of_autForm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RapidDecaySmallestRatioAbsorbsHeightAndCharacter
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeCoordinateLePowOfProdEqOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeCoordinateLePowOfProdEqOne
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

namespace GlobalTheory

theorem coneChain_step_bounds {a : ℕ} {t ρ K : ℝ} (ht : 0 < t) (hKt : t⁻¹ ≤ K) (hK0 : 0 ≤ K)
    (hρ0 : 0 ≤ ρ) (r : Fin a → ℝ) (hr : ∀ i, 0 < r i)
    (hup : ∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i)
    (hdown : ∀ i j : Fin a, (j : ℕ) = i + 1 → r i ≤ ρ * r j) :
    ∀ k : ℕ, ∀ i j : Fin a, (j : ℕ) = i + k → r j ≤ K ^ k * r i ∧ r i ≤ ρ ^ k * r j := by
  intro k
  induction k with
  | zero =>
    intro i j hij
    have hji : j = i := Fin.ext (by simpa using hij)
    subst hji
    simp
  | succ k ih =>
    intro i j hij
    have hja := j.isLt
    have hk : (i : ℕ) + k < a := by omega
    have h1 := ih i ⟨(i : ℕ) + k, hk⟩ rfl
    have hmj : (j : ℕ) = ((⟨(i : ℕ) + k, hk⟩ : Fin a) : ℕ) + 1 := by simp; omega
    have hu := hup _ j hmj
    have hd := hdown _ j hmj
    set m : Fin a := ⟨(i : ℕ) + k, hk⟩
    have hrj : r j ≤ t⁻¹ * r m := by
      rw [inv_mul_eq_div, le_div_iff₀ ht]; linarith
    constructor
    · calc r j ≤ t⁻¹ * r m := hrj
        _ ≤ K * r m := mul_le_mul_of_nonneg_right hKt (hr m).le
        _ ≤ K * (K ^ k * r i) := mul_le_mul_of_nonneg_left h1.1 hK0
        _ = K ^ (k + 1) * r i := by ring
    · calc r i ≤ ρ ^ k * r m := h1.2
        _ ≤ ρ ^ k * (ρ * r j) := mul_le_mul_of_nonneg_left hd (pow_nonneg hρ0 _)
        _ = ρ ^ (k + 1) * r j := by ring

theorem coneCoord_le_pow_of_prod_eq_one : ∀ (a : ℕ) (t : ℝ), 0 < t → ∃ C : ℝ, 1 ≤ C ∧
    ∀ (r : Fin a → ℝ) (ρ : ℝ), (∀ i, 0 < r i) →
      (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) → ∏ i, r i = 1 → 1 ≤ ρ →
      (∀ i j : Fin a, (j : ℕ) = i + 1 → r i ≤ ρ * r j) →
      ∀ i, r i ≤ C * ρ ^ a ∧ (r i)⁻¹ ≤ C * ρ ^ a := by
  intro a t ht
  obtain ⟨K, hK1, hKt⟩ : ∃ K : ℝ, 1 ≤ K ∧ t⁻¹ ≤ K := ⟨max 1 t⁻¹, le_max_left _ _, le_max_right _ _⟩
  refine ⟨K ^ a, one_le_pow₀ hK1, ?_⟩
  intro r ρ hr hup hprod hρ hdown i
  have hK0 : (0 : ℝ) ≤ K := by linarith
  have hρ0 : (0 : ℝ) ≤ ρ := by linarith
  have hC0 : 0 ≤ K ^ a * ρ ^ a := mul_nonneg (pow_nonneg hK0 _) (pow_nonneg hρ0 _)
  have step := coneChain_step_bounds ht hKt hK0 hρ0 r hr hup hdown
  have pair : ∀ p q : Fin a, r p ≤ K ^ a * ρ ^ a * r q := by
    intro p q
    rcases le_total (q : ℕ) p with h | h
    · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h
      have hka : k ≤ a := by have := p.isLt; omega
      calc r p ≤ K ^ k * r q := (step k q p hk).1
        _ ≤ K ^ a * ρ ^ a * r q := by
          apply mul_le_mul_of_nonneg_right _ (hr q).le
          calc K ^ k ≤ K ^ a := pow_le_pow_right₀ hK1 hka
            _ = K ^ a * 1 := by ring
            _ ≤ K ^ a * ρ ^ a := mul_le_mul_of_nonneg_left (one_le_pow₀ hρ) (pow_nonneg hK0 _)
    · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h
      have hka : k ≤ a := by have := q.isLt; omega
      calc r p ≤ ρ ^ k * r q := (step k p q hk).2
        _ ≤ K ^ a * ρ ^ a * r q := by
          apply mul_le_mul_of_nonneg_right _ (hr q).le
          calc ρ ^ k ≤ ρ ^ a := pow_le_pow_right₀ hρ hka
            _ = 1 * ρ ^ a := by ring
            _ ≤ K ^ a * ρ ^ a := mul_le_mul_of_nonneg_right (one_le_pow₀ hK1) (pow_nonneg hρ0 _)
  have hne : (Finset.univ : Finset (Fin a)).Nonempty := ⟨i, Finset.mem_univ _⟩
  have ex_le : ∃ j, r j ≤ 1 := by
    by_contra hcon
    push_neg at hcon
    have := Finset.prod_lt_prod_of_nonempty₀ (s := Finset.univ) (f := fun _ => (1 : ℝ)) (g := r)
      (fun _ _ => one_pos) (fun j _ => hcon j) hne
    simp [hprod] at this
  have ex_ge : ∃ j, 1 ≤ r j := by
    by_contra hcon
    push_neg at hcon
    have := Finset.prod_lt_prod_of_nonempty₀ (s := Finset.univ) (f := r) (g := fun _ => (1 : ℝ))
      (fun j _ => hr j) (fun j _ => hcon j) hne
    simp [hprod] at this
  obtain ⟨j, hj⟩ := ex_le
  obtain ⟨l, hl⟩ := ex_ge
  constructor
  · calc r i ≤ K ^ a * ρ ^ a * r j := pair i j
      _ ≤ K ^ a * ρ ^ a * 1 := mul_le_mul_of_nonneg_left hj hC0
      _ = K ^ a * ρ ^ a := by ring
  · rw [inv_eq_one_div, div_le_iff₀ (hr i)]
    have := pair l i
    linarith

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeCoordinateLePowOfProdEqOneStatement
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coneCoordinate_le_pow_of_prod_eq_one : ∀ (a : ℕ) (t : ℝ), 0 < t → ∃ C : ℝ, 1 ≤ C ∧ ∀ (r : Fin a → ℝ) (ρ : ℝ), (∀ i, 0 < r i) → (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) → ∏ i, r i = 1 → 1 ≤ ρ → (∀ i j : Fin a, (j : ℕ) = i + 1 → r i ≤ ρ * r j) → ∀ i, r i ≤ C * ρ ^ a ∧ (r i)⁻¹ ≤ C * ρ ^ a := by
  first | exact @GlobalTheory.coneCoord_le_pow_of_prod_eq_one | exact GlobalTheory.coneCoord_le_pow_of_prod_eq_one | (intros; apply GlobalTheory.coneCoord_le_pow_of_prod_eq_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RapidDecaySmallestRatioAbsorbsHeightAndCharacter
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

namespace GlobalTheory.RapidDecayReal

theorem height_le (a : ℕ) (N : ℕ) (r : Fin a → ℝ) (hr : ∀ i, 0 < r i) (K : ℝ)
    (hb : ∀ i, r i ≤ K ∧ (r i)⁻¹ ≤ K) :
    (1 + ∑ i, r i + ∑ i, (r i)⁻¹) ^ N ≤ (1 + 2 * a * K) ^ N := by
  have h0 : 0 ≤ 1 + ∑ i, r i + ∑ i, (r i)⁻¹ := by
    have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => (hr i).le)
    have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => (inv_pos.2 (hr i)).le)
    linarith
  apply pow_le_pow_left₀ h0
  have h1 : ∑ i, r i ≤ ∑ _i : Fin a, K := Finset.sum_le_sum (fun i _ => (hb i).1)
  have h2 : ∑ i, (r i)⁻¹ ≤ ∑ _i : Fin a, K := Finset.sum_le_sum (fun i _ => (hb i).2)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1 h2
  linarith

theorem char_ge (a : ℕ) (lam : Fin a → ℝ) (L : ℕ) (hL : ∑ i, |lam i| ≤ L) (r : Fin a → ℝ)
    (hr : ∀ i, 0 < r i) (K : ℝ) (hK : 1 ≤ K) (hb : ∀ i, r i ≤ K ∧ (r i)⁻¹ ≤ K) :
    (K ^ L)⁻¹ ≤ ∏ i, r i ^ lam i := by
  have hK0 : 0 < K := by linarith
  have hi : ∀ i, K ^ (-|lam i|) ≤ r i ^ lam i := by
    intro i
    rcases le_or_gt 0 (lam i) with h | h
    · rw [abs_of_nonneg h, Real.rpow_neg hK0.le, ← Real.inv_rpow hK0.le]
      apply Real.rpow_le_rpow (inv_nonneg.2 hK0.le) _ h
      rw [inv_le_comm₀ hK0 (hr i)]; exact (hb i).2
    · rw [abs_of_neg h, neg_neg]
      have e1 : K ^ lam i = (K⁻¹) ^ (-lam i) := by
        rw [Real.inv_rpow hK0.le, Real.rpow_neg hK0.le, inv_inv]
      have e2 : r i ^ lam i = ((r i)⁻¹) ^ (-lam i) := by
        rw [Real.inv_rpow (hr i).le, Real.rpow_neg (hr i).le, inv_inv]
      rw [e1, e2]
      apply Real.rpow_le_rpow (inv_nonneg.2 hK0.le) _ (by linarith)
      exact inv_anti₀ (hr i) (hb i).1
  calc (K ^ L)⁻¹ = K ^ (-(L : ℝ)) := by rw [Real.rpow_neg hK0.le, Real.rpow_natCast]
    _ ≤ K ^ (∑ i, -|lam i|) := by
        apply Real.rpow_le_rpow_of_exponent_le hK
        rw [Finset.sum_neg_distrib]; linarith
    _ = ∏ i, K ^ (-|lam i|) := Real.rpow_sum_of_pos hK0 _ _
    _ ≤ ∏ i, r i ^ lam i :=
        Finset.prod_le_prod₀ (fun i _ => Real.rpow_nonneg hK0.le _) (fun i _ => hi i)

theorem key (a : ℕ) (lam : Fin a → ℝ) (L N : ℕ) (hL : ∑ i, |lam i| ≤ L) (C0 : ℝ) (hC0 : 1 ≤ C0)
    (r : Fin a → ℝ) (hr : ∀ i, 0 < r i) (ρ : ℝ) (hρ : 1 ≤ ρ)
    (hb : ∀ i, r i ≤ C0 * ρ ^ a ∧ (r i)⁻¹ ≤ C0 * ρ ^ a) :
    (ρ ^ (a * N + a * L))⁻¹ * (1 + ∑ i, r i + ∑ i, (r i)⁻¹) ^ N ≤
      ((1 + 2 * a * C0) ^ N * C0 ^ L) * ∏ i, r i ^ lam i := by
  set P := ρ ^ a with hPdef
  have hP : 1 ≤ P := one_le_pow₀ hρ
  have hC00 : 0 < C0 := by linarith
  have hP0 : 0 < P := by linarith
  have hK : 1 ≤ C0 * P := by nlinarith
  have h1 := height_le a N r hr (C0 * P) hb
  have h2 := char_ge a lam L hL r hr (C0 * P) hK hb
  have h3 : (1 + 2 * (a : ℝ) * (C0 * P)) ^ N ≤ ((1 + 2 * a * C0) * P) ^ N := by
    apply pow_le_pow_left₀ (by positivity)
    nlinarith
  have hm : ρ ^ (a * N + a * L) = P ^ N * P ^ L := by
    rw [hPdef, ← pow_mul, ← pow_mul, ← pow_add]
  rw [hm]
  calc (P ^ N * P ^ L)⁻¹ * (1 + ∑ i, r i + ∑ i, (r i)⁻¹) ^ N
      ≤ (P ^ N * P ^ L)⁻¹ * ((1 + 2 * a * C0) * P) ^ N :=
        mul_le_mul_of_nonneg_left (h1.trans h3) (by positivity)
    _ = ((1 + 2 * a * C0) ^ N * C0 ^ L) * ((C0 * P) ^ L)⁻¹ := by
        rw [mul_pow, mul_pow]
        field_simp
    _ ≤ ((1 + 2 * a * C0) ^ N * C0 ^ L) * ∏ i, r i ^ lam i :=
        mul_le_mul_of_nonneg_left h2 (by positivity)

end GlobalTheory.RapidDecayReal


open GlobalTheory.RapidDecayReal in
theorem GlobalTheory.rapidDecay_real : ∀ (a : ℕ) (t : ℝ), 0 < t → ∀ (lam : Fin a → ℝ) (N : ℕ), ∃ (m : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ r : Fin a → ℝ, (∀ i, 0 < r i) → (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) → ∏ i, r i = 1 → (1 + ∑ i, r i + ∑ i, (r i)⁻¹) ^ N ≤ C * ∏ i, r i ^ lam i ∨ ∃ i j : Fin a, (j : ℕ) = i + 1 ∧ (r j / r i) ^ m * (1 + ∑ i, r i + ∑ i, (r i)⁻¹) ^ N ≤ C * ∏ i, r i ^ lam i := by
  intro a t ht lam N
  obtain ⟨C0, hC0, hC⟩ := GlobalTheory.T.coneCoordinate_le_pow_of_prod_eq_one a t ht
  set L := ⌈∑ i, |lam i|⌉₊ with hLdef
  have hL : ∑ i, |lam i| ≤ L := Nat.le_ceil _
  refine ⟨a * N + a * L, (1 + 2 * a * C0) ^ N * C0 ^ L, by positivity, ?_⟩
  intro r hr hcone hprod
  by_cases hall : ∀ i j : Fin a, (j : ℕ) = i + 1 → r i ≤ r j
  · left
    have hb := hC r 1 hr hcone hprod le_rfl (fun i j hij => by rw [one_mul]; exact hall i j hij)
    have := key a lam L N hL C0 hC0 r hr 1 le_rfl hb
    simpa using this
  · right
    push_neg at hall
    obtain ⟨i, j, hij, hlt⟩ := hall
    set S := (Finset.univ : Finset (Fin a × Fin a)).filter (fun p => (p.2 : ℕ) = p.1 + 1) with hS
    have hne : S.Nonempty := ⟨(i, j), by simp [hS, hij]⟩
    obtain ⟨p, hp, hmax⟩ := Finset.exists_max_image S (fun p => r p.1 / r p.2) hne
    have hpadj : (p.2 : ℕ) = p.1 + 1 := by simpa [hS] using hp
    have hij' : r i / r j ≤ r p.1 / r p.2 := hmax (i, j) (by simp [hS, hij])
    have hρ : 1 ≤ r p.1 / r p.2 := by
      have : 1 < r i / r j := by rw [one_lt_div (hr j)]; exact hlt
      linarith
    have hadj : ∀ i' j' : Fin a, (j' : ℕ) = i' + 1 → r i' ≤ (r p.1 / r p.2) * r j' := by
      intro i' j' h'
      have := hmax (i', j') (by simp [hS, h'])
      rwa [div_le_iff₀ (hr j')] at this
    have hb := hC r _ hr hcone hprod hρ hadj
    refine ⟨p.1, p.2, hpadj, ?_⟩
    have := key a lam L N hL C0 hC0 r hr _ hρ hb
    rw [← inv_div (r p.1) (r p.2), inv_pow]
    exact this
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RapidDecaySmallestRatioAbsorbsHeightAndCharacterStatement
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rapidDecay_smallestRatio_absorbs_height_and_character : ∀ (a : ℕ) (t : ℝ), 0 < t → ∀ (lam : Fin a → ℝ) (N : ℕ), ∃ (m : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ r : Fin a → ℝ, (∀ i, 0 < r i) → (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) → ∏ i, r i = 1 → (1 + ∑ i, r i + ∑ i, (r i)⁻¹) ^ N ≤ C * ∏ i, r i ^ lam i ∨ ∃ i j : Fin a, (j : ℕ) = i + 1 ∧ (r j / r i) ^ m * (1 + ∑ i, r i + ∑ i, (r i)⁻¹) ^ N ≤ C * ∏ i, r i ^ lam i := by
  first | exact @GlobalTheory.rapidDecay_real | exact GlobalTheory.rapidDecay_real | (intros; apply GlobalTheory.rapidDecay_real <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightPositiveDiagonalLeSumAddInv
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightPositiveDiagonalLeSumAddInv
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

namespace GlobalTheory

theorem height_diagonal_le_sum (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (r : Fin a → ℝ)
    (d : GL (Fin a) (Cinf E)) (hr : ∀ i, 0 < r i)
    (hd : d.val = Matrix.diagonal (fun i => fun _ => (r i : ℂ))) :
    height d ≤ 1 + ∑ i, r i + ∑ i, (r i)⁻¹ := by
  classical
  have hinv : (d⁻¹).val = Matrix.diagonal (fun i => fun _ => (((r i)⁻¹ : ℝ) : ℂ)) := by
    apply Units.inv_eq_of_mul_eq_one_right
    rw [hd, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i w
    have : (r i : ℂ) ≠ 0 := by exact_mod_cast (hr i).ne'
    simp [this]
  have key : ∀ s : Fin a → ℝ, (∀ i, 0 < s i) →
      ‖toL (Matrix.diagonal (fun i => fun (_ : InfinitePlace E) => ((s i : ℝ) : ℂ)))‖ ≤ ∑ i, s i := by
    intro s hs
    have h0 : 0 ≤ ∑ i, s i := Finset.sum_nonneg fun i _ => (hs i).le
    refine (pi_norm_le_iff_of_nonneg h0).2 fun i => (pi_norm_le_iff_of_nonneg h0).2 fun j =>
      (pi_norm_le_iff_of_nonneg h0).2 fun w => ?_
    change ‖(Matrix.diagonal (fun i => fun (_ : InfinitePlace E) => ((s i : ℝ) : ℂ))) i j w‖ ≤ _
    by_cases hij : i = j
    · subst hij
      rw [Matrix.diagonal_apply_eq, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hs i)]
      exact Finset.single_le_sum (fun k _ => (hs k).le) (Finset.mem_univ i)
    · rw [Matrix.diagonal_apply_ne _ hij]
      simpa using h0
  have h1 := key r hr
  have h2 := key (fun i => (r i)⁻¹) (fun i => inv_pos.2 (hr i))
  unfold GlobalTheory.CuspRep.height
  rw [hd, hinv]
  linarith

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightPositiveDiagonalLeSumAddInvStatement
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_positiveDiagonal_le_sum_add_inv : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (r : Fin a → ℝ) (d : GL (Fin a) (Cinf E)), (∀ i, 0 < r i) → d.val = Matrix.diagonal (fun i => fun _ => (r i : ℂ)) → height d ≤ 1 + ∑ i, r i + ∑ i, (r i)⁻¹ := by
  first | exact @GlobalTheory.height_diagonal_le_sum | exact GlobalTheory.height_diagonal_le_sum | (intros; apply GlobalTheory.height_diagonal_le_sum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormRapidDecaySiegelConeRealPoints
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

namespace GlobalTheory

theorem cuspForm_rapidDecay_siegel : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ψ : Sm E a), IsCuspForm ψ → ∀ (Ω : Set (GL (Fin a) (Cinf E))), IsCompact Ω → ∀ t : ℝ, 0 < t → ∀ lam : Fin a → ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : Fin a → ℝ) (d : GL (Fin a) (Cinf E)), (∀ i, 0 < r i) → (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) → d.val = Matrix.diagonal (fun i => fun _ => (r i : ℂ)) → ∏ i, r i = 1 → ∀ c ∈ Ω, ‖ψ.1 (infGL E a (d * c))‖ ≤ C * ∏ i, r i ^ lam i := by
  intro hP E _ _ _ a ψ hψ Ω hΩ t ht lam
  obtain ⟨N, hN⟩ := GlobalTheory.T.automorphicForm_GL_uniform_moderate_growth hP E a ψ hψ.1
  obtain ⟨m, C1, hC1, hreal⟩ := GlobalTheory.T.rapidDecay_smallestRatio_absorbs_height_and_character a t ht lam N
  obtain ⟨B, hB1, hB⟩ := GlobalTheory.T.exists_height_mul_le_of_isCompact E a Ω hΩ
  obtain ⟨C0, hC0⟩ := hN []
  simp only [List.map_nil, List.prod_nil, Module.End.one_apply] at hC0
  have hC0' : ∀ y, ‖ψ.1 (infGL E a y)‖ ≤ max C0 0 * height y ^ N := fun y =>
    (hC0 y).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (pow_nonneg (by linarith [one_le_height y]) _))
  have hex : ∀ i j : Fin a, ∃ C : ℝ, 0 ≤ C ∧ ((j : ℕ) = i + 1 → ∀ (r : Fin a → ℝ)
      (d : GL (Fin a) (Cinf E)), (∀ i, 0 < r i) → (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) →
      d.val = Matrix.diagonal (fun i => fun _ => (r i : ℂ)) →
      ∀ c ∈ Ω, ‖ψ.1 (infGL E a (d * c))‖ ≤ C * (r j / r i) ^ m * height d ^ N) := by
    intro i j
    by_cases hij : (j : ℕ) = i + 1
    · obtain ⟨C, hC, h⟩ := GlobalTheory.T.cuspForm_GL_iterated_decay_moderateGrowth hP E a N t ht i j hij m ψ hψ hN Ω hΩ
      exact ⟨C, hC, fun _ => h⟩
    · exact ⟨0, le_rfl, fun h => absurd h hij⟩
  choose Cf hCf0 hCf using hex
  have hS0 : 0 ≤ ∑ p : Fin a × Fin a, Cf p.1 p.2 := Finset.sum_nonneg fun p _ => hCf0 p.1 p.2
  have hK0 : 0 ≤ max C0 0 * B ^ N := mul_nonneg (le_max_right _ _) (pow_nonneg (by linarith) _)
  refine ⟨(max C0 0 * B ^ N + ∑ p : Fin a × Fin a, Cf p.1 p.2) * C1,
    mul_nonneg (add_nonneg hK0 hS0) hC1, ?_⟩
  intro r d hr hrt hd hprod c hc
  have hhd : height d ^ N ≤ (1 + ∑ i, r i + ∑ i, (r i)⁻¹) ^ N :=
    pow_le_pow_left₀ (by linarith [one_le_height d]) (GlobalTheory.T.height_positiveDiagonal_le_sum_add_inv E a r d hr hd) N
  have hP0 : 0 ≤ ∏ i, r i ^ lam i := Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hr i).le _
  have hsplit : (max C0 0 * B ^ N + ∑ p : Fin a × Fin a, Cf p.1 p.2) * C1 * ∏ i, r i ^ lam i
      = max C0 0 * B ^ N * (C1 * ∏ i, r i ^ lam i)
        + (∑ p : Fin a × Fin a, Cf p.1 p.2) * (C1 * ∏ i, r i ^ lam i) := by ring
  have hA := mul_nonneg hK0 (mul_nonneg hC1 hP0)
  have hB' := mul_nonneg hS0 (mul_nonneg hC1 hP0)
  rcases hreal r hr hrt hprod with h1 | ⟨i, j, hij, h2⟩
  · have hdc : height (d * c) ^ N ≤ (B * height d) ^ N :=
      pow_le_pow_left₀ (by linarith [one_le_height (d * c)]) (hB c hc d) N
    calc ‖ψ.1 (infGL E a (d * c))‖ ≤ max C0 0 * height (d * c) ^ N := hC0' _
      _ ≤ max C0 0 * (B * height d) ^ N := mul_le_mul_of_nonneg_left hdc (le_max_right _ _)
      _ = max C0 0 * B ^ N * height d ^ N := by rw [mul_pow]; ring
      _ ≤ max C0 0 * B ^ N * (1 + ∑ i, r i + ∑ i, (r i)⁻¹) ^ N := mul_le_mul_of_nonneg_left hhd hK0
      _ ≤ max C0 0 * B ^ N * (C1 * ∏ i, r i ^ lam i) := mul_le_mul_of_nonneg_left h1 hK0
      _ ≤ _ := by rw [hsplit]; linarith
  · have hq : 0 ≤ (r j / r i) ^ m := pow_nonneg (div_nonneg (hr j).le (hr i).le) _
    have hle : Cf i j ≤ ∑ p : Fin a × Fin a, Cf p.1 p.2 :=
      Finset.single_le_sum (f := fun p : Fin a × Fin a => Cf p.1 p.2) (fun p _ => hCf0 p.1 p.2)
        (Finset.mem_univ (i, j))
    calc ‖ψ.1 (infGL E a (d * c))‖ ≤ Cf i j * (r j / r i) ^ m * height d ^ N :=
          hCf i j hij r d hr hrt hd c hc
      _ ≤ Cf i j * ((r j / r i) ^ m * (1 + ∑ i, r i + ∑ i, (r i)⁻¹) ^ N) := by
          rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hhd hq) (hCf0 i j)
      _ ≤ Cf i j * (C1 * ∏ i, r i ^ lam i) := mul_le_mul_of_nonneg_left h2 (hCf0 i j)
      _ ≤ (∑ p : Fin a × Fin a, Cf p.1 p.2) * (C1 * ∏ i, r i ^ lam i) :=
          mul_le_mul_of_nonneg_right hle (mul_nonneg hC1 hP0)
      _ ≤ _ := by rw [hsplit]; linarith

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormRapidDecaySiegelConeRealPointsStatement
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspForm_rapidDecay_siegelCone_realPoints : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ψ : Sm E a), IsCuspForm ψ → ∀ (Ω : Set (GL (Fin a) (Cinf E))), IsCompact Ω → ∀ t : ℝ, 0 < t → ∀ lam : Fin a → ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : Fin a → ℝ) (d : GL (Fin a) (Cinf E)), (∀ i, 0 < r i) → (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) → d.val = Matrix.diagonal (fun i => fun _ => (r i : ℂ)) → ∏ i, r i = 1 → ∀ c ∈ Ω, ‖ψ.1 (infGL E a (d * c))‖ ≤ C * ∏ i, r i ^ lam i := by
  first | exact @GlobalTheory.cuspForm_rapidDecay_siegel | exact GlobalTheory.cuspForm_rapidDecay_siegel | (intros; apply GlobalTheory.cuspForm_rapidDecay_siegel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelSetAdelicGLExistsCompactDecomposition
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactConeDiagonalConjUpperTriangular
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactConeDiagonalConjUpperTriangular
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

namespace GlobalTheory

noncomputable def upperConeRescale {E : Type} [Field E] (a : ℕ) (N : Matrix (Fin a) (Fin a) ℝ)
    (M : Matrix (Fin a) (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E) :=
  Matrix.of fun p q => (fun _ => ((N p q : ℝ) : ℂ)) * M p q

lemma continuous_upperConeRescale {E : Type} [Field E] (a : ℕ) :
    Continuous (fun x : Matrix (Fin a) (Fin a) ℝ × Matrix (Fin a) (Fin a) (Cinf E) => upperConeRescale a x.1 x.2) := by
  refine continuous_pi fun p => continuous_pi fun q => ?_
  simp only [upperConeRescale, Matrix.of_apply]
  refine Continuous.mul ?_ ?_
  · refine continuous_pi fun _ => ?_
    exact Complex.continuous_ofReal.comp ((continuous_apply q).comp ((continuous_apply p).comp continuous_fst))
  · exact (continuous_apply q).comp ((continuous_apply p).comp continuous_snd)

lemma upperCone_conj_diag_eq {E : Type} [Field E] (a : ℕ) (r : Fin a → ℝ) (hr : ∀ i, 0 < r i)
    (d : GL (Fin a) (Cinf E)) (hd : d.val = Matrix.diagonal (fun i => fun _ => (r i : ℂ)))
    (M : Matrix (Fin a) (Fin a) (Cinf E)) (hM : M.BlockTriangular id) :
    (d⁻¹).val * M * d.val = upperConeRescale a (fun p q => if p ≤ q then r q / r p else 0) M := by
  have hD : (d⁻¹).val = Matrix.diagonal (fun i => fun _ => ((r i)⁻¹ : ℂ)) := by
    have h1 : d.val * Matrix.diagonal (fun i => fun _ => ((r i)⁻¹ : ℂ)) = 1 := by
      rw [hd, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext i x
      have : (r i : ℂ) ≠ 0 := by exact_mod_cast (hr i).ne'
      simp [this]
    calc (d⁻¹).val = (d⁻¹).val * (d.val * Matrix.diagonal (fun i => fun _ => ((r i)⁻¹ : ℂ))) := by
          rw [h1, mul_one]
      _ = _ := by rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
  rw [hD, hd]
  ext p q x
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [upperConeRescale, Matrix.of_apply, Pi.mul_apply]
  by_cases hpq : p ≤ q
  · rw [if_pos hpq]
    have : (r p : ℂ) ≠ 0 := by exact_mod_cast (hr p).ne'
    push_cast
    field_simp
  · rw [if_neg hpq]
    have h0 : M p q = 0 := hM (lt_of_not_ge hpq)
    simp [h0]

end GlobalTheory

theorem GlobalTheory.upperCone_conj_compact : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ω : Set (GL (Fin a) (Cinf E))), IsCompact ω → (∀ b ∈ ω, b.val.BlockTriangular id) → ∀ t : ℝ, 0 < t → ∃ Ω : Set (GL (Fin a) (Cinf E)), IsCompact Ω ∧ ∀ (r : Fin a → ℝ) (d : GL (Fin a) (Cinf E)), (∀ i, 0 < r i) → (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) → d.val = Matrix.diagonal (fun i => fun _ => (r i : ℂ)) → ∀ b ∈ ω, d⁻¹ * b * d ∈ Ω := by
  intro E _ _ _ a ω hω htri t ht
  obtain ⟨C, hC0, hC⟩ := GlobalTheory.T.cone_coordinate_ratio_bounded a t ht
  set K : Set (Matrix (Fin a) (Fin a) ℝ) := Set.univ.pi (fun _ => Set.univ.pi (fun _ => Set.Icc (0:ℝ) C)) with hK
  have hKc : IsCompact K := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc
  set A : Set (Matrix (Fin a) (Fin a) (Cinf E)) :=
    (fun x : Matrix (Fin a) (Fin a) ℝ × GL (Fin a) (Cinf E) => GlobalTheory.upperConeRescale a x.1 x.2.val) '' (K ×ˢ ω)
  set B : Set (Matrix (Fin a) (Fin a) (Cinf E)) :=
    (fun x : Matrix (Fin a) (Fin a) ℝ × GL (Fin a) (Cinf E) => GlobalTheory.upperConeRescale a x.1 (x.2⁻¹).val) '' (K ×ˢ ω)
  have hAc : IsCompact A := (hKc.prod hω).image
    ((GlobalTheory.continuous_upperConeRescale (E := E) a).comp (continuous_fst.prodMk (Units.continuous_val.comp continuous_snd)))
  have hBc : IsCompact B := (hKc.prod hω).image
    ((GlobalTheory.continuous_upperConeRescale (E := E) a).comp (continuous_fst.prodMk (Units.continuous_coe_inv.comp continuous_snd)))
  refine ⟨Units.embedProduct _ ⁻¹' (A ×ˢ (MulOpposite.op '' B)), ?_, ?_⟩
  · exact Units.isClosedEmbedding_embedProduct.isCompact_preimage
      (hAc.prod (hBc.image MulOpposite.continuous_op))
  intro r d hr hcone hd b hb
  have hN : (fun p q : Fin a => if p ≤ q then r q / r p else 0) ∈ K := by
    simp only [hK, Set.mem_pi]
    intro p _ q _
    rw [Set.mem_Icc]
    by_cases hpq : p ≤ q
    · simp only [if_pos hpq]
      exact ⟨div_nonneg (hr q).le (hr p).le, hC r hr hcone p q hpq⟩
    · simp only [if_neg hpq]
      exact ⟨le_rfl, hC0⟩
  have hbinv : (b⁻¹).val.BlockTriangular id := by
    have := Units.invertible b
    rw [Matrix.coe_units_inv]
    exact Matrix.blockTriangular_inv_of_blockTriangular (htri b hb)
  refine ⟨?_, ?_⟩
  · refine ⟨(_, b), ⟨hN, hb⟩, ?_⟩
    simp only [Units.val_mul]
    exact (GlobalTheory.upperCone_conj_diag_eq a r hr d hd b.val (htri b hb)).symm
  · refine ⟨(d⁻¹ * b * d)⁻¹.val, ⟨(_, b), ⟨hN, hb⟩, ?_⟩, rfl⟩
    have : (d⁻¹ * b * d)⁻¹ = d⁻¹ * b⁻¹ * d := by group
    simp only [this, Units.val_mul]
    exact (GlobalTheory.upperCone_conj_diag_eq a r hr d hd (b⁻¹).val hbinv).symm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactConeDiagonalConjUpperTriangularStatement
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compact_coneDiagonal_conj_upperTriangular : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ω : Set (GL (Fin a) (Cinf E))), IsCompact ω → (∀ b ∈ ω, b.val.BlockTriangular id) → ∀ t : ℝ, 0 < t → ∃ Ω : Set (GL (Fin a) (Cinf E)), IsCompact Ω ∧ ∀ (r : Fin a → ℝ) (d : GL (Fin a) (Cinf E)), (∀ i, 0 < r i) → (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) → d.val = Matrix.diagonal (fun i => fun _ => (r i : ℂ)) → ∀ b ∈ ω, d⁻¹ * b * d ∈ Ω := by
  first | exact @GlobalTheory.upperCone_conj_compact | exact GlobalTheory.upperCone_conj_compact | (intros; apply GlobalTheory.upperCone_conj_compact <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelSetAdelicGLExistsCompactDecomposition
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

open Pointwise Matrix

namespace GlobalTheory.SiegelSetGL

variable (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)

theorem continuous_pInfC : Continuous (pInf E) :=
  continuous_pi fun w =>
    ((InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      (continuous_apply w)).comp continuous_fst

theorem continuous_mapInf : Continuous (GeneralLinearGroup.map (n := Fin a) (pInf E)) :=
  Continuous.units_map _ (continuous_id.matrix_map (continuous_pInfC E))

theorem continuous_mapFin : Continuous (GeneralLinearGroup.map (n := Fin a) (pFin E)) :=
  Continuous.units_map _ (continuous_id.matrix_map (continuous_snd : Continuous (pFin E)))

theorem exists_compact_decomp : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (ω : Set (AdelicGLn.AdelicGL E a)), IsCompact ω →
    ω ⊆ (adelicBorel (K := E) (n := a) : Set (AdelicGLn.AdelicGL E a)) → ∀ t : ℝ, 0 < t →
    ∃ (Ω : Set (GL (Fin a) (Cinf E))) (Kf : Set (GL (Fin a) (Af E))), IsCompact Ω ∧ IsCompact Kf ∧
      ∀ (r : Fin a → ℝ) (d : GL (Fin a) (Cinf E)), (∀ i, 0 < r i) → (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) →
        d.val = Matrix.diagonal (fun i => fun _ => (r i : ℂ)) → ∀ b ∈ ω, ∀ k ∈ maxCompact (K := E) (n := a),
          ∃ c ∈ Ω, ∃ f ∈ Kf, b * infGL E a d * k = infGL E a (d * c) * finGL E a f := by
  intro E _ _ _ a ω hω hωB t ht
  set pI := GeneralLinearGroup.map (n := Fin a) (pInf E)
  set pF := GeneralLinearGroup.map (n := Fin a) (pFin E)
  have hωI : IsCompact (pI '' ω) := hω.image (continuous_mapInf E a)
  have hup : ∀ b ∈ pI '' ω, b.val.BlockTriangular id := by
    rintro _ ⟨b, hb, rfl⟩ i j hij
    have h0 : (b : Matrix (Fin a) (Fin a) (Ad E)) i j = 0 := hωB hb hij
    change pInf E ((b : Matrix (Fin a) (Fin a) (Ad E)) i j) = 0
    rw [h0, map_zero]
  obtain ⟨Ω0, hΩ0, hΩ⟩ := GlobalTheory.T.exists_compact_coneDiagonal_conj_upperTriangular E a (pI '' ω) hωI hup t ht
  have hK := isCompact_maxCompact (K := E) (n := a)
  refine ⟨Ω0 * pI '' (maxCompact (K := E) (n := a) : Set (AdelicGLn.AdelicGL E a)),
    pF '' ω * pF '' (maxCompact (K := E) (n := a) : Set (AdelicGLn.AdelicGL E a)),
    hΩ0.mul (hK.image (continuous_mapInf E a)),
    (hω.image (continuous_mapFin E a)).mul (hK.image (continuous_mapFin E a)), ?_⟩
  intro r d hr hrt hd b hb k hk
  refine ⟨(d⁻¹ * pI b * d) * pI k, Set.mul_mem_mul (hΩ r d hr hrt hd _ ⟨b, hb, rfl⟩) ⟨k, hk, rfl⟩,
    pF b * pF k, Set.mul_mem_mul ⟨b, hb, rfl⟩ ⟨k, hk, rfl⟩, ?_⟩
  apply ga_ext
  · change pI (b * infGL E a d * k) = pI (infGL E a (d * (d⁻¹ * pI b * d * pI k)) * finGL E a (pF b * pF k))
    simp only [map_mul, pI, pInf_infGL, pInf_finGL, mul_one]
    group
  · change pF (b * infGL E a d * k) = pF (infGL E a (d * (d⁻¹ * pI b * d * pI k)) * finGL E a (pF b * pF k))
    simp only [map_mul, pF, pFin_infGL, pFin_finGL, mul_one, one_mul]

end GlobalTheory.SiegelSetGL
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelSetAdelicGLExistsCompactDecompositionStatement
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelSet_adelicGL_exists_compact_decomposition : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ω : Set (AdelicGLn.AdelicGL E a)), IsCompact ω → ω ⊆ (adelicBorel (K := E) (n := a) : Set (AdelicGLn.AdelicGL E a)) → ∀ t : ℝ, 0 < t → ∃ (Ω : Set (GL (Fin a) (Cinf E))) (Kf : Set (GL (Fin a) (Af E))), IsCompact Ω ∧ IsCompact Kf ∧ ∀ (r : Fin a → ℝ) (d : GL (Fin a) (Cinf E)), (∀ i, 0 < r i) → (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) → d.val = Matrix.diagonal (fun i => fun _ => (r i : ℂ)) → ∀ b ∈ ω, ∀ k ∈ maxCompact (K := E) (n := a), ∃ c ∈ Ω, ∃ f ∈ Kf, b * infGL E a d * k = infGL E a (d * c) * finGL E a f := by
  first | exact @GlobalTheory.SiegelSetGL.exists_compact_decomp | exact GlobalTheory.SiegelSetGL.exists_compact_decomp | (intros; apply GlobalTheory.SiegelSetGL.exists_compact_decomp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTranslatesSmoothFunctionOfCompact
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTranslatesSmoothFunctionOfCompact
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

namespace GlobalTheory

theorem finite_translates_of_isCompact (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]
    (a : ℕ) (φ : Sm E a) (h : IsOpen {k | finRep E a k φ = φ})
    (Kf : Set (GL (Fin a) (Af E))) (hK : IsCompact Kf) :
    ∃ S : Finset (GL (Fin a) (Af E)), ∀ f ∈ Kf, ∃ f' ∈ S,
      finRep E a f φ = finRep E a f' φ := by
  have hn : ∀ f ∈ Kf, {g | finRep E a g φ = finRep E a f φ} ∈ nhds f := by
    intro f _
    have hc : Continuous (fun g : GL (Fin a) (Af E) => f⁻¹ * g) :=
      continuous_const.mul continuous_id
    have ho := h.preimage hc
    refine Filter.mem_of_superset (ho.mem_nhds ?_) ?_
    · simp
    · intro g hg
      have hg' : finRep E a (f⁻¹ * g) φ = φ := hg
      have e : g = f * (f⁻¹ * g) := by simp
      show finRep E a g φ = finRep E a f φ
      calc finRep E a g φ = finRep E a (f * (f⁻¹ * g)) φ := by rw [← e]
        _ = finRep E a f (finRep E a (f⁻¹ * g) φ) := by rw [map_mul]; rfl
        _ = finRep E a f φ := by rw [hg']
  obtain ⟨t, -, ht⟩ := hK.elim_nhds_subcover (fun f => {g | finRep E a g φ = finRep E a f φ}) hn
  refine ⟨t, fun f hf => ?_⟩
  have := ht hf
  simp only [Set.mem_iUnion] at this
  obtain ⟨f', hf', h'⟩ := this
  exact ⟨f', hf', h'⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTranslatesSmoothFunctionOfCompactStatement
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_translates_smoothFunction_of_compact : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a), IsOpen {k | finRep E a k φ = φ} → ∀ Kf : Set (GL (Fin a) (Af E)), IsCompact Kf → ∃ S : Finset (GL (Fin a) (Af E)), ∀ f ∈ Kf, ∃ f' ∈ S, finRep E a f φ = finRep E a f' φ := by
  first | exact @GlobalTheory.finite_translates_of_isCompact | exact GlobalTheory.finite_translates_of_isCompact | (intros; apply GlobalTheory.finite_translates_of_isCompact <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealDiagonalInfGLEqPositiveIdeleDiagonal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealDiagonalInfGLEqPositiveIdeleDiagonal
noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic
  GroundTheory.Automorphic.Reduction

namespace GlobalTheory.SiegelTorusInf

theorem exists_diag_infGL (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (r : Fin a → ℝ)
    (hr : ∀ i, 0 < r i) : ∃ d : GL (Fin a) (Cinf E), d.val = Matrix.diagonal (fun i => fun _ => (r i : ℂ)) ∧
      diagUnits a (fun i => posIdele (K := E) (r i) (hr i)) = infGL E a d := by
  have h0 : ∀ i, (r i : ℂ) ≠ 0 := fun i => Complex.ofReal_ne_zero.2 (hr i).ne'
  refine ⟨⟨Matrix.diagonal (fun i => fun _ => (r i : ℂ)), Matrix.diagonal (fun i => fun _ => (r i : ℂ)⁻¹), ?_, ?_⟩,
    rfl, ?_⟩
  · rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i w
    exact mul_inv_cancel₀ (h0 i)
  · rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i w
    exact inv_mul_cancel₀ (h0 i)
  · have key : ∀ i, ((posIdele (K := E) (r i) (hr i) : IdeleGroup E) : Ad E) =
        1 - sInf E 1 + sInf E (fun _ => (r i : ℂ)) := fun i => by
      rw [GlobalTheory.CuspBoundSiegel.posIdele_congr (hr i) (Real.exp_pos _) (Real.exp_log (hr i)).symm,
        GlobalTheory.CuspBoundSiegel.posIdele_exp]
      change 1 - sInf E 1 + sInf E _ = _
      congr 2
      funext w
      change Complex.exp (Real.log (r i) : ℂ) = (r i : ℂ)
      rw [← Complex.ofReal_exp, Real.exp_log (hr i)]
    refine Units.ext ?_
    rw [coe_diagUnits]
    refine Matrix.ext fun i j => ?_
    change _ = (1 : Matrix (Fin a) (Fin a) (Ad E)) i j - sInf E ((1 : Matrix (Fin a) (Fin a) (Cinf E)) i j) +
      sInf E (Matrix.diagonal (fun i => (fun _ => (r i : ℂ) : Cinf E)) i j)
    by_cases h : i = j
    · subst h
      rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, Matrix.one_apply_eq, Matrix.one_apply_eq]
      exact key i
    · rw [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h, Matrix.one_apply_ne h,
        map_zero, sub_zero, add_zero]

end GlobalTheory.SiegelTorusInf

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealDiagonalInfGLEqPositiveIdeleDiagonalStatement
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_realDiagonal_infGL_eq_positiveIdeleDiagonal : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (r : Fin a → ℝ) (hr : ∀ i, 0 < r i), ∃ d : GL (Fin a) (Cinf E), d.val = Matrix.diagonal (fun i => fun _ => (r i : ℂ)) ∧ diagUnits a (fun i => posIdele (K := E) (r i) (hr i)) = infGL E a d := by
  first | exact @GlobalTheory.SiegelTorusInf.exists_diag_infGL | exact GlobalTheory.SiegelTorusInf.exists_diag_infGL | (intros; apply GlobalTheory.SiegelTorusInf.exists_diag_infGL <;> assumption)
end
end

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

namespace GlobalTheory

theorem cuspRapidDecaySiegelGL_of_finite (hfin : GlobalTheory.Published.AutomorphicFormsFiniteGL) :
    GlobalTheory.Published.CuspRapidDecaySiegelGL := by
  intro E _ _ _ a φ hφ ω hω hωB _ t ht lam
  obtain ⟨Ω, Kf, hΩ, hKf, hgeom⟩ := GlobalTheory.T.siegelSet_adelicGL_exists_compact_decomposition E a ω hω hωB t ht
  obtain ⟨S, hS⟩ := GlobalTheory.T.finite_translates_smoothFunction_of_compact E a φ hφ.1.level Kf hKf
  have hcore := fun f' : GL (Fin a) (Af E) =>
    GlobalTheory.T.cuspForm_rapidDecay_siegelCone_realPoints hfin E a (finRep E a f' φ) (GlobalTheory.T.isCuspForm_operator_act hfin E a (.fin f') φ hφ) Ω hΩ t ht lam
  choose C hC0 hC using hcore
  refine ⟨∑ f' ∈ S, C f', fun b hb r hr hchain hprod k hk => ?_⟩
  obtain ⟨d, hd, hdiag⟩ := GlobalTheory.T.exists_realDiagonal_infGL_eq_positiveIdeleDiagonal E a r hr
  rw [hdiag]
  obtain ⟨c, hc, f, hf, heq⟩ := hgeom r d hr hchain hd b hb k hk
  rw [heq]
  obtain ⟨f', hf', hff'⟩ := hS f hf
  have e : φ.1 (infGL E a (d * c) * finGL E a f) = (finRep E a f' φ).1 (infGL E a (d * c)) := by
    rw [← hff']; rfl
  rw [e]
  refine (hC f' r d hr hchain hd hprod c hc).trans ?_
  exact mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun i _ => hC0 i) hf')
    (Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hr i).le _)

end GlobalTheory
