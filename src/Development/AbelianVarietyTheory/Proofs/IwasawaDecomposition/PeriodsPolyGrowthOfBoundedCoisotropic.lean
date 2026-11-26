module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenMetricOnSet

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialGrowthMatrixMulBoundedVectors
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialGrowthMatrixMulBoundedVectors
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem matrix_mul_bounded_poly_growth : ∀ (n g d : ℕ) (R : Set (Fin n → ℂ)) (τ : (Fin n → ℂ) → Fin d → Fin d → ℂ) (E : (Fin n → ℂ) → Fin d → Fin g → ℂ), (∃ (C : ℝ) (k : ℕ), ∀ s ∈ R, ‖τ s‖ ≤ C * (1 + ‖s‖) ^ k) → (∀ i, ∃ C : ℝ, ∀ s ∈ R, ‖E s i‖ ≤ C) → ∀ j, ∃ (C : ℝ) (k : ℕ), ∀ s ∈ R, ‖∑ i, τ s i j • E s i‖ ≤ C * (1 + ‖s‖) ^ k := by
  intro n g d R τ E ⟨C, k, hC⟩ hE j
  choose C' hC' using hE
  refine ⟨max C 0 * ∑ i, max (C' i) 0, k, fun s hs => ?_⟩
  have hp : (0:ℝ) ≤ (1 + ‖s‖) ^ k := pow_nonneg (by positivity) _
  have h1 : ∀ i, ‖τ s i j‖ ≤ max C 0 * (1 + ‖s‖) ^ k := fun i =>
    (norm_le_pi_norm (τ s i) j).trans ((norm_le_pi_norm (τ s) i).trans
      ((hC s hs).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hp)))
  calc ‖∑ i, τ s i j • E s i‖ ≤ ∑ i, ‖τ s i j • E s i‖ := norm_sum_le _ _
    _ = ∑ i, ‖τ s i j‖ * ‖E s i‖ := by simp only [norm_smul]
    _ ≤ ∑ i, (max C 0 * (1 + ‖s‖) ^ k) * max (C' i) 0 :=
        Finset.sum_le_sum fun i _ => mul_le_mul (h1 i) (le_max_of_le_left (hC' i s hs))
          (norm_nonneg _) (mul_nonneg (le_max_right _ _) hp)
    _ = max C 0 * (∑ i, max (C' i) 0) * (1 + ‖s‖) ^ k := by rw [← Finset.mul_sum]; ring

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialGrowthMatrixMulBoundedVectorsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polynomial_growth_matrix_mul_bounded_vectors : ∀ (n g d : ℕ) (R : Set (Fin n → ℂ)) (τ : (Fin n → ℂ) → Fin d → Fin d → ℂ) (E : (Fin n → ℂ) → Fin d → Fin g → ℂ), (∃ (C : ℝ) (k : ℕ), ∀ s ∈ R, ‖τ s‖ ≤ C * (1 + ‖s‖) ^ k) → (∀ i, ∃ C : ℝ, ∀ s ∈ R, ‖E s i‖ ≤ C) → ∀ j, ∃ (C : ℝ) (k : ℕ), ∀ s ∈ R, ‖∑ i, τ s i j • E s i‖ ≤ C * (1 + ‖s‖) ^ k := by
  first | exact @GlobalTheory.matrix_mul_bounded_poly_growth | exact GlobalTheory.matrix_mul_bounded_poly_growth | (intros; apply GlobalTheory.matrix_mul_bounded_poly_growth <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermFormImRealCombinationEqDotProduct
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermFormImRealCombinationEqDotProduct
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.hermForm_im_real_comb (g r : ℕ) (x : Fin r → Fin g → ℂ) (M : Matrix (Fin r) (Fin r) ℝ) (Hm : Matrix (Fin g) (Fin g) ℂ)
    (h : ∀ i j, (hermForm Hm (x i) (x j)).im = M i j) (u v : Fin r → ℝ) :
    (hermForm Hm (∑ m, (u m : ℂ) • x m) (∑ m, (v m : ℂ) • x m)).im = u ⬝ᵥ M *ᵥ v := by
  have key : hermForm Hm (∑ m, (u m : ℂ) • x m) (∑ m, (v m : ℂ) • x m)
      = ∑ m, ∑ m', ((u m * v m' : ℝ) : ℂ) * hermForm Hm (x m) (x m') := by
    simp only [hermForm, star_sum, star_smul, Matrix.mulVec_sum, Matrix.mulVec_smul, sum_dotProduct,
      dotProduct_sum, smul_dotProduct, dotProduct_smul, smul_eq_mul, Complex.star_def, Complex.conj_ofReal]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun m' _ => ?_
    push_cast
    ring
  rw [key]
  simp only [Complex.im_sum, Complex.im_ofReal_mul, h, dotProduct, Matrix.mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun m' _ => ?_
  ring
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermFormImRealCombinationEqDotProductStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermForm_im_real_combination_eq_dotProduct : ∀ (g r : ℕ) (x : Fin r → Fin g → ℂ) (M : Matrix (Fin r) (Fin r) ℝ) (Hm : Matrix (Fin g) (Fin g) ℂ), (∀ i j, (hermForm Hm (x i) (x j)).im = M i j) → ∀ u v : Fin r → ℝ, (hermForm Hm (∑ m, (u m : ℂ) • x m) (∑ m, (v m : ℂ) • x m)).im = u ⬝ᵥ M *ᵥ v := by
  first | exact @GlobalTheory.hermForm_im_real_comb | exact GlobalTheory.hermForm_im_real_comb | (intros; apply GlobalTheory.hermForm_im_real_comb <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialGrowthOfSpanningCombinations
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialGrowthOfSpanningCombinations
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem growth_bound_of_spanning_combinations : ∀ (n g r : ℕ) (J : Type) [Fintype J] (R : Set (Fin n → ℂ)) (x : (Fin n → ℂ) → Fin r → Fin g → ℂ) (u : J → Fin r → ℝ), Submodule.span ℝ (Set.range u) = ⊤ → (∀ i, ∃ (C : ℝ) (k : ℕ), ∀ s ∈ R, ‖∑ m, (u i m : ℂ) • x s m‖ ≤ C * (1 + ‖s‖) ^ k) → ∃ (C : ℝ) (k : ℕ), ∀ s ∈ R, ‖x s‖ ≤ C * (1 + ‖s‖) ^ k := by
  intro n g r J _ R x u hspan hb
  choose C k hC using hb
  have hsingle : ∀ m : Fin r, ∃ a : J → ℝ, ∑ i, a i • u i = Pi.single m 1 := by
    intro m
    have hmem : (Pi.single m (1:ℝ) : Fin r → ℝ) ∈ Submodule.span ℝ (Set.range u) := by
      rw [hspan]; trivial
    exact (Submodule.mem_span_range_iff_exists_fun ℝ).1 hmem
  choose a ha using hsingle
  refine ⟨∑ m, ∑ i, |a m i| * max (C i) 0, ∑ i, k i, ?_⟩
  intro s hs
  have h1 : (1:ℝ) ≤ 1 + ‖s‖ := by linarith [norm_nonneg s]
  have hpow : ∀ i, (1 + ‖s‖) ^ (k i) ≤ (1 + ‖s‖) ^ (∑ j, k j) := fun i =>
    pow_le_pow_right₀ h1 (Finset.single_le_sum (fun j _ => Nat.zero_le (k j)) (Finset.mem_univ i))
  have hm : ∀ m, ‖x s m‖ ≤ (∑ i, |a m i| * max (C i) 0) * (1 + ‖s‖) ^ (∑ j, k j) := by
    intro m
    have hid : x s m = ∑ i, (a m i : ℂ) • ∑ m', (u i m' : ℂ) • x s m' := by
      have e := congrFun (ha m)
      simp only [Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      have hc : ∀ m', ∑ i, ((a m i : ℂ) * (u i m' : ℂ)) • x s m'
          = (((Pi.single m (1:ℝ) : Fin r → ℝ) m' : ℝ) : ℂ) • x s m' := by
        intro m'
        rw [← Finset.sum_smul]
        congr 1
        have h2 := e m'
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h2
        rw [← h2]; push_cast; rfl
      rw [Finset.sum_congr rfl (fun m' _ => hc m')]
      rw [Finset.sum_eq_single m]
      · simp
      · intro b _ hb; simp [Pi.single_apply, hb]
      · intro h; exact absurd (Finset.mem_univ m) h
    rw [hid]
    calc ‖∑ i, (a m i : ℂ) • ∑ m', (u i m' : ℂ) • x s m'‖
        ≤ ∑ i, ‖(a m i : ℂ) • ∑ m', (u i m' : ℂ) • x s m'‖ := norm_sum_le _ _
      _ ≤ ∑ i, |a m i| * (max (C i) 0 * (1 + ‖s‖) ^ (∑ j, k j)) := by
        apply Finset.sum_le_sum; intro i _
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        calc _ ≤ C i * (1 + ‖s‖) ^ (k i) := hC i s hs
          _ ≤ max (C i) 0 * (1 + ‖s‖) ^ (k i) :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
          _ ≤ max (C i) 0 * (1 + ‖s‖) ^ (∑ j, k j) :=
              mul_le_mul_of_nonneg_left (hpow i) (le_max_right _ _)
      _ = _ := by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => (_root_.mul_assoc _ _ _).symm
  have hnn : ∀ m, 0 ≤ ∑ i, |a m i| * max (C i) 0 := fun m =>
    Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) (le_max_right _ _)
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg (Finset.sum_nonneg fun m _ => hnn m) (by positivity))).2 fun m => ?_
  calc ‖x s m‖ ≤ _ := hm m
    _ ≤ (∑ m, ∑ i, |a m i| * max (C i) 0) * (1 + ‖s‖) ^ (∑ j, k j) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact Finset.single_le_sum (f := fun m => ∑ i, |a m i| * max (C i) 0)
        (fun j _ => hnn j) (Finset.mem_univ m)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialGrowthOfSpanningCombinationsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polynomial_growth_of_spanning_combinations : ∀ (n g r : ℕ) (J : Type) [Fintype J] (R : Set (Fin n → ℂ)) (x : (Fin n → ℂ) → Fin r → Fin g → ℂ) (u : J → Fin r → ℝ), Submodule.span ℝ (Set.range u) = ⊤ → (∀ i, ∃ (C : ℝ) (k : ℕ), ∀ s ∈ R, ‖∑ m, (u i m : ℂ) • x s m‖ ≤ C * (1 + ‖s‖) ^ k) → ∃ (C : ℝ) (k : ℕ), ∀ s ∈ R, ‖x s‖ ≤ C * (1 + ‖s‖) ^ k := by
  first | exact @GlobalTheory.growth_bound_of_spanning_combinations | exact GlobalTheory.growth_bound_of_spanning_combinations | (intros; apply GlobalTheory.growth_bound_of_spanning_combinations <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinearIndependentRealCombinationsOfIndependent
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinearIndependentRealCombinationsOfIndependent
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem linearIndependent_real_combination (g r d : ℕ) (x : Fin r → Fin g → ℂ)
    (e : Fin d → Fin r → ℝ) (hx : LinearIndependent ℝ x) (he : LinearIndependent ℝ e) :
    LinearIndependent ℝ (fun i => ∑ m, (e i m : ℂ) • x m) := by
  rw [Fintype.linearIndependent_iff] at hx he ⊢
  intro c hc
  have hreal : ∀ i, (∑ m, (e i m : ℂ) • x m) = ∑ m, e i m • x m := by
    intro i
    refine Finset.sum_congr rfl fun m _ => ?_
    funext k
    simp [Pi.smul_apply, Complex.real_smul]
  have h1 : ∑ m, (∑ i, c i * e i m) • x m = 0 := by
    have h0 : ∑ i, c i • ∑ m, e i m • x m = 0 := by
      simpa only [hreal] using hc
    rw [← h0]
    simp_rw [Finset.smul_sum, smul_smul, Finset.sum_smul]
    exact Finset.sum_comm
  have h2 := hx _ h1
  refine he c ?_
  funext m
  simpa [Finset.sum_apply, Pi.smul_apply] using h2 m

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinearIndependentRealCombinationsOfIndependentStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearIndependent_real_combinations_of_independent : ∀ (g r d : ℕ) (x : Fin r → Fin g → ℂ) (e : Fin d → Fin r → ℝ), LinearIndependent ℝ x → LinearIndependent ℝ e → LinearIndependent ℝ (fun i => ∑ m, (e i m : ℂ) • x m) := by
  first | exact @GlobalTheory.linearIndependent_real_combination | exact GlobalTheory.linearIndependent_real_combination | (intros; apply GlobalTheory.linearIndependent_real_combination <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodsPolyGrowthOfBoundedCoisotropic
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam.Hor.LogCh.PerGrowth

theorem differentiableOn_matrix_det_of_entries_normedSpace {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {B : Set V} {d : ℕ}
    {A : V → Matrix (Fin d) (Fin d) ℂ} (hA : ∀ i j, DifferentiableOn ℂ (fun b => A b i j) B) :
    DifferentiableOn ℂ (fun b => (A b).det) B := by
  simp only [Matrix.det_apply']
  refine DifferentiableOn.fun_sum fun σ _ => DifferentiableOn.const_mul ?_ _
  have key : ∀ t : Finset (Fin d), DifferentiableOn ℂ (fun b => ∏ i ∈ t, A b (σ i) i) B := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp
    | insert a t ha ih =>
      simp only [Finset.prod_insert ha]
      exact (hA _ _).mul ih
  exact key _

theorem differentiableOn_matrix_inv_apply_of_entries {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {B : Set V} {d : ℕ}
    {A : V → Matrix (Fin d) (Fin d) ℂ} (hA : ∀ i j, DifferentiableOn ℂ (fun b => A b i j) B)
    (hd : ∀ b ∈ B, (A b).det ≠ 0) (i j : Fin d) :
    DifferentiableOn ℂ (fun b => (A b)⁻¹ i j) B := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul, Matrix.adjugate_apply]
  refine ((differentiableOn_matrix_det_of_entries_normedSpace hA).inv hd).mul (differentiableOn_matrix_det_of_entries_normedSpace fun a b => ?_)
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact differentiableOn_const _
  · exact hA _ _

theorem lam_polyGrowth_of_coisotropic : ∀ (n a g r : ℕ) (lam : (Fin n → ℂ) → Fin r → Fin g → ℂ) (M : Matrix (Fin r) (Fin r) ℝ) (W : Submodule ℝ (Fin r → ℝ)), DifferentiableOn ℂ lam (logDom n a) → (∀ s ∈ logDom n a, LinearIndependent ℝ (lam s) ∧ Submodule.span ℝ (Set.range (lam s)) = ⊤ ∧ ∃ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ ∀ i j, (hermForm Hm (lam s i) (lam s j)).im = M i j) → (∀ v : Fin r → ℝ, (∀ w ∈ W, v ⬝ᵥ M *ᵥ w = 0) → v ∈ W) → (∀ w ∈ W, ∃ C : ℝ, ∀ s ∈ logDom n a, ‖logExp a s‖ ≤ 1 / 2 → ‖∑ j, (w j : ℂ) • lam s j‖ ≤ C) → ∃ (C : ℝ) (k : ℕ), ∀ s ∈ logDom n a, ‖logExp a s‖ ≤ 1 / 2 → (∀ j : Fin n, (j : ℕ) < a → |(s j).im| ≤ Real.pi) → ‖lam s‖ ≤ C * (1 + ‖s‖) ^ k := by
  intro n a g r lam M W hd hs hW hb
  by_cases hne : (logDom n a).Nonempty
  swap
  · exact ⟨0, 0, fun s hs' => absurd ⟨s, hs'⟩ hne⟩
  obtain ⟨s0, hs0⟩ := hne
  obtain ⟨hli0, hsp0, Hm0, hH0, hP0, hM0⟩ := hs s0 hs0
  obtain ⟨hMa, hMd, hr⟩ := GlobalTheory.T.hermForm_periods_alternating_nondeg_rank_eq_two_mul g r (lam s0) M Hm0 hli0 hsp0 hH0 hP0 hM0
  obtain ⟨d, e, f, heW, hee, hfe, hsp⟩ := GlobalTheory.T.exists_lagrangian_dual_pair_in_coisotropic r M W hMa hMd hW
  obtain ⟨hli, hrd⟩ := GlobalTheory.T.isotropicDual_family_linearIndependent_rank_eq_two_mul r d M e f hee hfe hsp
  obtain rfl : d = g := by omega
  obtain ⟨E, hE⟩ : ∃ E : (Fin n → ℂ) → Fin d → Fin d → ℂ, E = fun s i => ∑ m, (e i m : ℂ) • lam s m := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F : (Fin n → ℂ) → Fin d → Fin d → ℂ, F = fun s j => ∑ m, (f j m : ℂ) • lam s m := ⟨_, rfl⟩
  obtain ⟨Em, hEm⟩ : ∃ Em : (Fin n → ℂ) → Matrix (Fin d) (Fin d) ℂ, Em = fun s => Matrix.of fun k i => E s i k :=
    ⟨_, rfl⟩
  obtain ⟨Fm, hFm⟩ : ∃ Fm : (Fin n → ℂ) → Matrix (Fin d) (Fin d) ℂ, Fm = fun s => Matrix.of fun k j => F s j k :=
    ⟨_, rfl⟩
  obtain ⟨τ, hτ⟩ : ∃ τ : (Fin n → ℂ) → Fin d → Fin d → ℂ, τ = fun s i j => ((Em s)⁻¹ * Fm s) i j := ⟨_, rfl⟩
  have hlinE : LinearIndependent ℝ e := hli.comp Sum.inl Sum.inl_injective

  have hpt : ∀ s ∈ logDom n a, (Em s).det ≠ 0 ∧ (∀ j, F s j = ∑ i, τ s i j • E s i) ∧
      (∀ v : Fin d → ℝ, v ≠ 0 → 0 < (∑ i, ∑ j, (v i : ℂ) * τ s i j * (v j : ℂ)).im) ∧
      ∀ i j, τ s i j - τ s j i = ((f i ⬝ᵥ M *ᵥ f j : ℝ) : ℂ) := by
    intro s hs'
    obtain ⟨hli1, -, Hm, hH, hP, hMs⟩ := hs s hs'
    have h6 := GlobalTheory.T.hermForm_im_real_combination_eq_dotProduct d r (lam s) M Hm hMs
    have hEE : ∀ i j, (hermForm Hm (E s i) (E s j)).im = 0 := fun i j => by
      rw [hE]; exact (h6 _ _).trans (hee i j)
    have hFE : ∀ i j, (hermForm Hm (F s i) (E s j)).im = if i = j then 1 else 0 := fun i j => by
      rw [hE, hF]; exact (h6 _ _).trans (hfe i j)
    have hFF : ∀ i j, (hermForm Hm (F s i) (F s j)).im = f i ⬝ᵥ M *ᵥ f j := fun i j => by
      rw [hF]; exact h6 _ _
    have hEli : LinearIndependent ℝ (E s) := by
      rw [hE]; exact GlobalTheory.T.linearIndependent_real_combinations_of_independent d r d (lam s) e hli1 hlinE
    have hdet : (Em s).det ≠ 0 := by rw [hEm]; exact GlobalTheory.T.det_ne_zero_of_real_independent_isotropic_hermitian d Hm (E s) hP hEli hEE
    have hFt : ∀ j, F s j = ∑ i, τ s i j • E s i := by
      intro j
      have hm := Matrix.mul_nonsing_inv_cancel_left (Em s) (Fm s) (Ne.isUnit hdet)
      funext k
      have := congrFun (congrFun hm k) j
      have hEmk : ∀ k i, Em s k i = E s i k := fun k i => by simp [hEm]
      have hFmk : ∀ k i, Fm s k i = F s i k := fun k i => by simp [hFm]
      rw [Matrix.mul_apply] at this
      simp only [hEmk, hFmk] at this
      rw [hτ]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [← this]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    obtain ⟨h4a, h4b⟩ := GlobalTheory.T.riemann_relations_period_matrix_hermitian d d Hm (E s) (F s) (τ s) hH hP hFt hEE hFE
    exact ⟨hdet, hFt, h4a, fun i j => (h4b i j).trans (by rw [hFF])⟩

  have hlam : ∀ m k, DifferentiableOn ℂ (fun s => lam s m k) (logDom n a) := fun m k =>
    differentiableOn_pi.1 (differentiableOn_pi.1 hd m) k
  have hEmd : ∀ k i, DifferentiableOn ℂ (fun s => Em s k i) (logDom n a) := fun k i => by
    simp only [hEm, hE, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact DifferentiableOn.fun_sum fun m _ => (hlam m k).const_mul _
  have hFmd : ∀ k i, DifferentiableOn ℂ (fun s => Fm s k i) (logDom n a) := fun k i => by
    simp only [hFm, hF, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact DifferentiableOn.fun_sum fun m _ => (hlam m k).const_mul _
  have hτd : DifferentiableOn ℂ τ (logDom n a) := by
    refine differentiableOn_pi.2 fun i => differentiableOn_pi.2 fun j => ?_
    simp only [hτ, Matrix.mul_apply]
    exact DifferentiableOn.fun_sum fun l _ =>
      (differentiableOn_matrix_inv_apply_of_entries hEmd (fun s hs' => (hpt s hs').1) i l).mul (hFmd l j)
  obtain ⟨C, k, hC⟩ := GlobalTheory.T.periodMatrix_polynomialGrowth_puncturedPolydisc n a d τ (fun i j => ((f i ⬝ᵥ M *ᵥ f j : ℝ) : ℂ)) hτd (fun s hs' => (hpt s hs').2.2.1)
    (fun s hs' => (hpt s hs').2.2.2)
  set R : Set (Fin n → ℂ) := {s | s ∈ logDom n a ∧ ‖logExp a s‖ ≤ 1 / 2 ∧
    ∀ j : Fin n, (j : ℕ) < a → |(s j).im| ≤ Real.pi} with hR
  have hEb : ∀ i, ∃ C : ℝ, ∀ s ∈ R, ‖E s i‖ ≤ C := fun i => by
    obtain ⟨C, hC⟩ := hb (e i) (heW i)
    exact ⟨C, fun s hs' => by rw [hE]; exact hC s hs'.1 hs'.2.1⟩
  have h9 := GlobalTheory.T.polynomial_growth_matrix_mul_bounded_vectors n d d R τ E ⟨C, k, fun s hs' => hC s hs'.1 hs'.2.1 hs'.2.2⟩ hEb
  obtain ⟨C', k', h8⟩ := GlobalTheory.T.polynomial_growth_of_spanning_combinations n d r (Fin d ⊕ Fin d) R lam (Sum.elim e f) hsp (fun i => by
    rcases i with i | j
    · obtain ⟨C, hC⟩ := hEb i
      exact ⟨C, 0, fun s hs' => by simpa [hE] using hC s hs'⟩
    · obtain ⟨C, k, hC⟩ := h9 j
      refine ⟨C, k, fun s hs' => ?_⟩
      have := (hpt s hs'.1).2.1 j
      simp only [hF] at this
      simp only [Sum.elim_inr]
      rw [this]
      exact hC s hs')
  exact ⟨C', k', fun s hs' h1 h2 => h8 s ⟨hs', h1, h2⟩⟩

end GlobalTheory.ShFam.Hor.LogCh.PerGrowth
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodsPolyGrowthOfBoundedCoisotropicStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periods_polyGrowth_of_bounded_coisotropic : ∀ (n a g r : ℕ) (lam : (Fin n → ℂ) → Fin r → Fin g → ℂ) (M : Matrix (Fin r) (Fin r) ℝ) (W : Submodule ℝ (Fin r → ℝ)), DifferentiableOn ℂ lam (logDom n a) → (∀ s ∈ logDom n a, LinearIndependent ℝ (lam s) ∧ Submodule.span ℝ (Set.range (lam s)) = ⊤ ∧ ∃ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ ∀ i j, (hermForm Hm (lam s i) (lam s j)).im = M i j) → (∀ v : Fin r → ℝ, (∀ w ∈ W, v ⬝ᵥ M *ᵥ w = 0) → v ∈ W) → (∀ w ∈ W, ∃ C : ℝ, ∀ s ∈ logDom n a, ‖logExp a s‖ ≤ 1 / 2 → ‖∑ j, (w j : ℂ) • lam s j‖ ≤ C) → ∃ (C : ℝ) (k : ℕ), ∀ s ∈ logDom n a, ‖logExp a s‖ ≤ 1 / 2 → (∀ j : Fin n, (j : ℕ) < a → |(s j).im| ≤ Real.pi) → ‖lam s‖ ≤ C * (1 + ‖s‖) ^ k := by
  first | exact @GlobalTheory.ShFam.Hor.LogCh.PerGrowth.lam_polyGrowth_of_coisotropic | exact GlobalTheory.ShFam.Hor.LogCh.PerGrowth.lam_polyGrowth_of_coisotropic | (intros; apply GlobalTheory.ShFam.Hor.LogCh.PerGrowth.lam_polyGrowth_of_coisotropic <;> assumption)
end
